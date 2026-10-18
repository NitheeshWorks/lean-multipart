import LeanMultipart.Proofs.MultipartStream
import LeanMultipart.Theory.Codec
import LeanMultipart.Specifications.Multipart

/-!
# The multipart round trip

`Mp.multipart_parse_print_ext`: the parser reads back exactly the parts
the printer wrote, followed by any epilogue, provided no part body contains
the delimiter `CR LF -- boundary` and each part's headers are well formed
and within the limits.
-/

namespace LeanMultipart
namespace Mp

/-! ## Distinct byte constants -/

@[simp] theorem byte_CR_ne_LF : (Byte.CR = Byte.LF) = False := by decide
@[simp] theorem byte_CR_ne_HYPHEN : (Byte.CR = Byte.HYPHEN) = False := by decide
@[simp] theorem byte_CR_ne_COLON : (Byte.CR = Byte.COLON) = False := by decide
@[simp] theorem byte_CR_ne_SPACE : (Byte.CR = Byte.SPACE) = False := by decide
@[simp] theorem byte_LF_ne_CR : (Byte.LF = Byte.CR) = False := by decide
@[simp] theorem byte_LF_ne_HYPHEN : (Byte.LF = Byte.HYPHEN) = False := by decide
@[simp] theorem byte_LF_ne_COLON : (Byte.LF = Byte.COLON) = False := by decide
@[simp] theorem byte_LF_ne_SPACE : (Byte.LF = Byte.SPACE) = False := by decide
@[simp] theorem byte_HYPHEN_ne_CR : (Byte.HYPHEN = Byte.CR) = False := by decide
@[simp] theorem byte_HYPHEN_ne_LF : (Byte.HYPHEN = Byte.LF) = False := by decide
@[simp] theorem byte_HYPHEN_ne_COLON : (Byte.HYPHEN = Byte.COLON) = False := by decide
@[simp] theorem byte_HYPHEN_ne_SPACE : (Byte.HYPHEN = Byte.SPACE) = False := by decide
@[simp] theorem byte_COLON_ne_CR : (Byte.COLON = Byte.CR) = False := by decide
@[simp] theorem byte_COLON_ne_LF : (Byte.COLON = Byte.LF) = False := by decide
@[simp] theorem byte_COLON_ne_HYPHEN : (Byte.COLON = Byte.HYPHEN) = False := by decide
@[simp] theorem byte_COLON_ne_SPACE : (Byte.COLON = Byte.SPACE) = False := by decide
@[simp] theorem byte_SPACE_ne_CR : (Byte.SPACE = Byte.CR) = False := by decide
@[simp] theorem byte_SPACE_ne_LF : (Byte.SPACE = Byte.LF) = False := by decide
@[simp] theorem byte_SPACE_ne_HYPHEN : (Byte.SPACE = Byte.HYPHEN) = False := by decide
@[simp] theorem byte_SPACE_ne_COLON : (Byte.SPACE = Byte.COLON) = False := by decide

variable (cx : Ctx)

/-- The delimiter, as a list. -/
abbrev D : Bytes := cx.boundary.delimL

theorem delim_data : cx.delim.data = (D cx).toArray := by rw [cx.h_delim]; rfl

theorem dlen_eq : cx.dlen = (D cx).length := by
  unfold Ctx.dlen
  show cx.delim.data.size = _
  rw [delim_data]; simp

theorem dlen_ge : 5 ≤ cx.dlen := by
  have h := cx.boundary.h_valid.1
  rw [dlen_eq]; simp [Boundary.delimL, Boundary.toList] at h ⊢; omega

theorem dAt_eq (k : Nat) (hk : k < cx.dlen) : cx.dAt k = (D cx)[k]'(by rw [← dlen_eq]; exact hk) := by
  unfold Ctx.dAt
  simp only [show k < cx.delim.size by unfold Ctx.dlen at hk; exact hk, ↓reduceDIte]
  simp [cx.h_delim, Boundary.delim, ByteArray.getElem_eq_getElem_data]

theorem D_get_succ (k : Nat) (hk : k + 1 < (D cx).length) :
    (D cx)[k + 1] = ([Byte.LF, Byte.HYPHEN, Byte.HYPHEN] ++ cx.boundary.toList)[k]'(by
      simp [Boundary.delimL] at hk ⊢; omega) := by
  simp [Boundary.delimL]

/-- The delimiter has `CR` only at its start. -/
theorem dAt_ne_CR (k : Nat) (h1 : 1 ≤ k) (hk : k < cx.dlen) : cx.dAt k ≠ Byte.CR := by
  rw [dAt_eq cx k hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [D_get_succ]
  have hb := cx.boundary.h_valid.2.2.1
  intro h
  have hmem : Byte.CR ∈ [Byte.LF, Byte.HYPHEN, Byte.HYPHEN] ++ cx.boundary.toList := h ▸ List.getElem_mem _
  have hne : ∀ x ∈ [Byte.LF, Byte.HYPHEN, Byte.HYPHEN], x ≠ Byte.CR := by decide
  rcases List.mem_append.1 hmem with h' | h'
  · exact hne _ h' rfl
  · exact absurd (hb _ h') (by decide)

theorem delim_toList : cx.delim.data.toList = D cx := by rw [delim_data]

theorem delim_extract_toList (k : Nat) : (cx.delim.extract 0 k).data.toList = (D cx).take k := by
  simp [ByteArray.data_extract, Array.toList_extract, delim_toList]


theorem D_drop2 : (D cx).drop 2 = Byte.HYPHEN :: (D cx).drop 3 := by
  simp [Boundary.delimL]

theorem D_drop_cons (k : Nat) (hk : k < (D cx).length) :
    (D cx).drop k = (D cx)[k] :: (D cx).drop (k + 1) := by
  simp

/-! ## The opening boundary line -/

theorem feed_sb (m : Nat) : ∀ (s : MState) (k : Nat), cx.dlen - (k + 2) = m → k + 2 ≤ cx.dlen →
    s.phase = .startBoundary k →
    feed cx s ((D cx).drop (k + 2)) =
      { s with phase := .startBoundary (cx.dlen - 2), pos := s.pos + (cx.dlen - (k + 2)) } := by
  induction m with
  | zero =>
    intro s k hm hk hp
    have : k + 2 = cx.dlen := by omega
    have hl : (D cx).drop (k + 2) = [] := by rw [this, dlen_eq]; simp
    rw [hl]
    cases s; simp_all [feed]; omega
  | succ m ih =>
    intro s k hm hk hp
    have hlt : k + 2 < (D cx).length := by rw [← dlen_eq]; omega
    rw [D_drop_cons cx (k + 2) hlt]
    have hs : step cx s ((D cx)[k + 2]) = { s with phase := .startBoundary (k + 1), pos := s.pos + 1 } := by
      have h2 : k + 2 < cx.dlen := by omega
      simp [step, hp, sbByte, h2, dAt_eq cx (k + 2) h2]
    simp only [feed, List.foldl_cons, hs]
    have := ih { s with phase := .startBoundary (k + 1), pos := s.pos + 1 } (k + 1) (by omega) (by omega) rfl
    simp only [feed] at this
    rw [this]
    simp; omega

/-- `--boundary CR LF` from the start begins a part. -/
theorem feed_open (s : MState) (hp : s.phase = .start) :
    feed cx s ((D cx).drop 2 ++ [Byte.CR, Byte.LF]) =
      beginPart { s with pos := s.pos + (cx.dlen - 2) + 2 } := by
  rw [D_drop2, feed_append]
  have h5 := dlen_ge cx
  have hs : step cx s Byte.HYPHEN = { s with phase := .startBoundary 1, pos := s.pos + 1 } := by
    have h2 : 0 + 2 < cx.dlen := by omega
    have hd : cx.dAt 2 = Byte.HYPHEN := by
      rw [dAt_eq cx 2 (by omega)]; simp [Boundary.delimL]
    simp [step, hp, sbByte, h2, hd]
  simp only [feed, List.foldl_cons, hs]
  have := feed_sb cx _ { s with phase := .startBoundary 1, pos := s.pos + 1 } 1 rfl (by omega) rfl
  simp only [feed] at this
  rw [show (D cx).drop 3 = (D cx).drop (1 + 2) by rfl, this]
  have hk : ¬ (cx.dlen - 2 + 2 < cx.dlen) := by omega
  simp [step, sbByte, hk, beginPart, show Byte.CR ≠ Byte.HYPHEN by decide]
  omega

/-- `--boundary--` from the start is the empty message. -/
theorem feed_open_empty (s : MState) (hp : s.phase = .start) :
    (feed cx s ((D cx).drop 2 ++ [Byte.HYPHEN, Byte.HYPHEN])).phase = .done ∧
    (feed cx s ((D cx).drop 2 ++ [Byte.HYPHEN, Byte.HYPHEN])).parts = s.parts := by
  rw [D_drop2, feed_append]
  have h5 := dlen_ge cx
  have hs : step cx s Byte.HYPHEN = { s with phase := .startBoundary 1, pos := s.pos + 1 } := by
    have h2 : 0 + 2 < cx.dlen := by omega
    have hd : cx.dAt 2 = Byte.HYPHEN := by
      rw [dAt_eq cx 2 (by omega)]; simp [Boundary.delimL]
    simp [step, hp, sbByte, h2, hd]
  simp only [feed, List.foldl_cons, hs]
  have := feed_sb cx _ { s with phase := .startBoundary 1, pos := s.pos + 1 } 1 rfl (by omega) rfl
  simp only [feed] at this
  rw [show (D cx).drop 3 = (D cx).drop (1 + 2) by rfl, this]
  have hk : ¬ (cx.dlen - 2 + 2 < cx.dlen) := by omega
  simp [step, sbByte, hk]

/-- In the `done` phase every byte is ignored (the epilogue). -/
theorem feed_done (s : MState) (hp : s.phase = .done) (l : Bytes) :
    (feed cx s l).phase = .done ∧ (feed cx s l).parts = s.parts := by
  induction l generalizing s with
  | nil => exact ⟨hp, rfl⟩
  | cons c cs ih =>
    simp only [feed, List.foldl_cons] at *
    have hs : step cx s c = { s with pos := s.pos + 1 } := by simp [step, hp]
    rw [hs]; exact ih _ hp


/-! ## Header lines -/

theorem token_ne_CR {c : UInt8} (h : Byte.isTokenChar c = true) : c ≠ Byte.CR := by
  rintro rfl; exact absurd h (by decide)
theorem token_ne_COLON {c : UInt8} (h : Byte.isTokenChar c = true) : c ≠ Byte.COLON := by
  rintro rfl; exact absurd h (by decide)

theorem push_append_toArray (a : ByteArray) (c : UInt8) (l : Bytes) :
    a.push c ++ ⟨l.toArray⟩ = a ++ ⟨(c :: l).toArray⟩ := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem feed_nameChars (t : Bytes) : ∀ (s : MState), s.phase = .headerField →
    (∀ c ∈ t, Byte.isTokenChar c = true) → s.hdrSize + t.length ≤ cx.cfg.maxHeaderSize →
    feed cx s t = { s with pos := s.pos + t.length, name := s.name ++ ⟨t.toArray⟩, hdrSize := s.hdrSize + t.length } := by
  induction t with
  | nil => intro s _ _ _; cases s; simp [feed]
  | cons c cs ih =>
    intro s hp ht hz
    have hc := ht c (by simp)
    have h1 : ¬ cx.cfg.maxHeaderSize < s.hdrSize + 1 := by simp at hz; omega
    have hs : step cx s c = { s with pos := s.pos + 1, phase := .headerField, hdrSize := s.hdrSize + 1, name := s.name.push c } := by
      simp [step, hp, headerFieldByte, h1, token_ne_COLON hc, hc]
    simp only [feed, List.foldl_cons, hs]
    have := ih { s with pos := s.pos + 1, phase := .headerField, hdrSize := s.hdrSize + 1, name := s.name.push c } rfl (fun x hx => ht x (by simp [hx])) (by simp at hz ⊢; omega)
    simp only [feed] at this
    rw [this, push_append_toArray]
    cases s; simp_all; omega

theorem feed_valueChars (t : Bytes) : ∀ (s : MState), s.phase = .headerValue →
    (∀ c ∈ t, c ≠ Byte.CR) → s.hdrSize + t.length ≤ cx.cfg.maxHeaderSize →
    feed cx s t = { s with pos := s.pos + t.length, value := s.value ++ ⟨t.toArray⟩, hdrSize := s.hdrSize + t.length } := by
  induction t with
  | nil => intro s _ _ _; cases s; simp [feed]
  | cons c cs ih =>
    intro s hp ht hz
    have hc := ht c (by simp)
    have h1 : ¬ cx.cfg.maxHeaderSize < s.hdrSize + 1 := by simp at hz; omega
    have hs : step cx s c = { s with pos := s.pos + 1, phase := .headerValue, hdrSize := s.hdrSize + 1, value := s.value.push c } := by
      simp [step, hp, headerValueByte, h1, hc]
    simp only [feed, List.foldl_cons, hs]
    have := ih { s with pos := s.pos + 1, phase := .headerValue, hdrSize := s.hdrSize + 1, value := s.value.push c } rfl (fun x hx => ht x (by simp [hx])) (by simp at hz ⊢; omega)
    simp only [feed] at this
    rw [this, push_append_toArray]
    cases s; simp_all; omega

/-- At the start of a header line, with empty buffers. -/
def HdrStart (s : MState) : Prop :=
  s.phase = .headerFieldStart ∧ s.name = ByteArray.empty ∧ s.value = ByteArray.empty ∧ s.hdrSize = 0

theorem ba_eta (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by cases b; simp

/-- From `headerValueStart`: optional value, `CR`, `LF`. -/
theorem feed_value_end (s : MState) (v : Bytes) (hp : s.phase = .headerValueStart)
    (hv : ∀ c ∈ v, c ≠ Byte.CR) (hsp : v.head? ≠ some Byte.SPACE)
    (hz : s.hdrSize + v.length ≤ cx.cfg.maxHeaderSize) (hval : s.value = ByteArray.empty) :
    feed cx s (v ++ [Byte.CR, Byte.LF]) =
      { s with pos := s.pos + v.length + 2, phase := .headerFieldStart, name := ByteArray.empty, value := ByteArray.empty, hdrSize := 0, headers := s.headers.push (s.name, ⟨v.toArray⟩) } := by
  cases v with
  | nil =>
    simp [feed, step, hp, headerValueByte, hval]
  | cons v0 vs =>
    have h0 := hv v0 (by simp)
    have hsp0 : v0 ≠ Byte.SPACE := by simpa using hsp
    have h1 : ¬ cx.cfg.maxHeaderSize < s.hdrSize + 1 := by simp at hz; omega
    have hs : step cx s v0 = { s with pos := s.pos + 1, phase := .headerValue, hdrSize := s.hdrSize + 1, value := s.value.push v0 } := by
      simp [step, hp, headerValueByte, h1, h0, hsp0]
    rw [List.cons_append, show feed cx s (v0 :: (vs ++ [Byte.CR, Byte.LF])) =
      feed cx (step cx s v0) (vs ++ [Byte.CR, Byte.LF]) from rfl, hs, feed_append,
      feed_valueChars cx vs _ rfl (fun x hx => hv x (by simp [hx])) (by simp at hz ⊢; omega)]
    simp [feed, step, headerValueByte, hval]
    refine ⟨by omega, ?_⟩
    congr 2

/-- One header line from the start of a line. -/
theorem feed_headerLine (s : MState) (hs : HdrStart s) (hc : s.hdrCount + 1 ≤ cx.cfg.maxHeaderCount)
    (h : ByteArray × ByteArray) (hw : WFHeader cx.cfg h) :
    feed cx s (headerLineL h) =
      { s with pos := s.pos + (headerLineL h).length, hdrCount := s.hdrCount + 1, headers := s.headers.push h } := by
  obtain ⟨hp, hn, hv, hz⟩ := hs
  obtain ⟨hne, htok, hcr, hsp, hlen⟩ := hw
  obtain ⟨n0, ns, hnl⟩ : ∃ n0 ns, h.1.data.toList = n0 :: ns := by
    cases hq : h.1.data.toList with
    | nil => exact absurd hq hne
    | cons a b => exact ⟨a, b, rfl⟩
  have ht0 := htok n0 (by simp [hnl])
  have hcnt : ¬ cx.cfg.maxHeaderCount < s.hdrCount + 1 := by omega
  have hsz1 : ¬ cx.cfg.maxHeaderSize < 0 + 1 := by rw [hnl] at hlen; simp at hlen; omega
  -- the first name byte
  have s1 : step cx s n0 = { s with pos := s.pos + 1, hdrCount := s.hdrCount + 1, phase := .headerField, hdrSize := 1, name := ByteArray.empty.push n0 } := by
    simp [step, hp, headerFieldByte, hcnt, token_ne_CR ht0, token_ne_COLON ht0, ht0, hsz1]
  have hlen' := hlen; rw [hnl] at hlen'; simp at hlen'
  have hline : headerLineL h =
      n0 :: (ns ++ (Byte.COLON :: Byte.SPACE :: (h.2.data.toList ++ [Byte.CR, Byte.LF]))) := by
    simp [headerLineL, hnl]
  have e1 : feed cx s (headerLineL h) =
      feed cx (feed cx (step cx s n0) ns) (Byte.COLON :: Byte.SPACE :: (h.2.data.toList ++ [Byte.CR, Byte.LF])) := by
    rw [hline]; simp only [feed, List.foldl_cons, List.foldl_append]
  rw [e1, s1, feed_nameChars cx ns _ rfl (fun x hx => htok x (by simp [hnl, hx])) (by simp; omega)]
  have e2 : ∀ (t : MState) (l : Bytes), feed cx t (Byte.COLON :: Byte.SPACE :: l) =
      feed cx (step cx (step cx t Byte.COLON) Byte.SPACE) l := fun _ _ => rfl
  rw [e2]
  have hcol : ¬ cx.cfg.maxHeaderSize < 1 + ns.length + 1 := by omega
  have hspc : ¬ cx.cfg.maxHeaderSize < 1 + ns.length + 1 + 1 := by omega
  have hnemp : (ByteArray.empty.push n0 ++ ⟨ns.toArray⟩).isEmpty = false := by
    simp [ByteArray.isEmpty, ByteArray.size_append]
  simp [step, headerFieldByte, hcol, hspc, hnemp]
  rw [feed_value_end cx _ h.2.data.toList rfl hcr hsp (by simp; omega) rfl]
  cases s
  simp only at hp hn hv hz ⊢
  subst hp hn hv hz
  simp only [MState.mk.injEq, true_and, and_true]
  constructor
  · rw [hline]; simp; omega
  · have e : ((ByteArray.empty.push n0 ++ ⟨ns.toArray⟩ : ByteArray), (⟨h.2.data.toList.toArray⟩ : ByteArray)) = h := by
      have : (ByteArray.empty.push n0 ++ ⟨ns.toArray⟩ : ByteArray) = ⟨h.1.data.toList.toArray⟩ := by
        apply ByteArray.ext; simp [ByteArray.data_append, hnl]
      rw [this, ba_eta, ba_eta]
    rw [e]


theorem feed_headers (hs : List (ByteArray × ByteArray)) : ∀ (s : MState), HdrStart s →
    s.hdrCount + hs.length ≤ cx.cfg.maxHeaderCount → (∀ h ∈ hs, WFHeader cx.cfg h) →
    feed cx s (hs.flatMap headerLineL) =
      { s with pos := s.pos + (hs.flatMap headerLineL).length, hdrCount := s.hdrCount + hs.length, headers := s.headers ++ hs.toArray } := by
  induction hs with
  | nil => intro s _ _ _; cases s; simp [feed]
  | cons h rest ih =>
    intro s hst hc hw
    rw [List.flatMap_cons, feed_append, feed_headerLine cx s hst (by simp at hc; omega) h (hw h (by simp))]
    obtain ⟨h1, h2, h3, h4⟩ := hst
    rw [ih { s with pos := s.pos + (headerLineL h).length, hdrCount := s.hdrCount + 1, headers := s.headers.push h } ⟨h1, h2, h3, h4⟩ (by simp at hc ⊢; omega) (fun x hx => hw x (by simp [hx]))]
    cases s; simp; constructor <;> (try omega)

/-- The empty line that ends the headers starts the body. -/
theorem feed_headersEnd (s : MState) (hs : HdrStart s) :
    feed cx s [Byte.CR, Byte.LF] = { s with pos := s.pos + 2, phase := .partData (.idx 0), data := ByteArray.empty } := by
  obtain ⟨hp, _, _, _⟩ := hs
  cases s; simp_all [feed, step]

/-! ## Part data -/

theorem infix_of_suffix {l₁ l₂ : Bytes} (h : l₁ <:+ l₂) : l₁ <:+: l₂ := h.isInfix

/-- Scanning a body that does not contain the delimiter: the data seen so
far, followed by the partial match, is everything read. -/
theorem feed_body (body : Bytes) : ∀ (s : MState) (k : Nat), s.phase = .partData (.idx k) → k < cx.dlen →
    ¬ (D cx) <:+: ((D cx).take k ++ body) →
    ∃ k', (feed cx s body).phase = .partData (.idx k') ∧ k' < cx.dlen ∧
      (feed cx s body).data.toList ++ (D cx).take k' = s.data.toList ++ (D cx).take k ++ body ∧
      (feed cx s body).headers = s.headers ∧ (feed cx s body).parts = s.parts := by
  induction body with
  | nil => intro s k hp hk _; exact ⟨k, hp, hk, by simp [feed], rfl, rfl⟩
  | cons c rest ih =>
    intro s k hp hk hinf
    simp only [feed, List.foldl_cons]
    have hkD : k < (D cx).length := by rw [← dlen_eq]; exact hk
    by_cases hc : c = cx.dAt k
    · -- the match extends
      have hcD : c = (D cx)[k] := by rw [hc, dAt_eq cx k hk]
      have hk1 : k + 1 ≠ cx.dlen := by
        intro he
        apply hinf
        have : (D cx).take k ++ [c] = D cx := by
          rw [hcD, ← List.take_succ_eq_append_getElem hkD, show k + 1 = (D cx).length by rw [← dlen_eq]; exact he]
          simp
        refine ⟨[], rest, ?_⟩
        rw [List.nil_append]
        conv => lhs; rw [← this]
        simp
      have hs : step cx s c = { s with pos := s.pos + 1, phase := .partData (.idx (k + 1)) } := by
        simp [step, hp, matchByte, ← hc, hk1]
      rw [hs]
      have htk : (D cx).take (k + 1) = (D cx).take k ++ [c] := by
        rw [hcD, List.take_succ_eq_append_getElem hkD]
      obtain ⟨k', h1, h2, h3, h4, h5⟩ := ih { s with pos := s.pos + 1, phase := .partData (.idx (k + 1)) } (k + 1)
        rfl (by omega) (by rw [htk]; simpa using hinf)
      refine ⟨k', h1, h2, ?_, h4, h5⟩
      simp only [feed] at h3; rw [h3, htk]; simp
    · -- mismatch: the partial match is data, and `c` is looked at afresh
      have hinf' : ¬ (D cx) <:+: (c :: rest) := fun h => hinf (h.trans (List.suffix_append _ _).isInfix)
      by_cases hcr : c = Byte.CR
      · subst hcr
        have hs : step cx s Byte.CR = { s with pos := s.pos + 1, phase := .partData (.idx 1), data := s.data ++ cx.delim.extract 0 k } := by
          simp [step, hp, matchByte, hc, restart] <;> (try (intro h; subst h; simp [ByteArray.extract_same]))
        rw [hs]
        have h1D : (D cx).take 1 = [Byte.CR] := by simp [Boundary.delimL]
        obtain ⟨k', h1, h2, h3, h4, h5⟩ := ih { s with pos := s.pos + 1, phase := .partData (.idx 1), data := s.data ++ cx.delim.extract 0 k } 1
          rfl (by have := dlen_ge cx; omega) (by rw [h1D]; simpa using hinf')
        refine ⟨k', h1, h2, ?_, h4, h5⟩
        simp only [feed] at h3; rw [h3, h1D]; simp [delim_toList]
      · have hs : step cx s c = { s with pos := s.pos + 1, phase := .partData (.idx 0), data := (s.data ++ cx.delim.extract 0 k).push c } := by
          simp [step, hp, matchByte, hc, restart, hcr] <;> (try (intro h; subst h; simp [ByteArray.extract_same]))
        rw [hs]
        obtain ⟨k', h1, h2, h3, h4, h5⟩ := ih { s with pos := s.pos + 1, phase := .partData (.idx 0), data := (s.data ++ cx.delim.extract 0 k).push c } 0
          rfl (by have := dlen_ge cx; omega)
          (by simp only [List.take_zero, List.nil_append]; exact fun h => hinf' (h.trans (List.suffix_cons _ _).isInfix))
        refine ⟨k', h1, h2, ?_, h4, h5⟩
        simp only [feed] at h3; rw [h3]; simp [delim_toList]

/-- From a partial match of `j` bytes, the rest of the delimiter completes it. -/
theorem feed_matchFrom (m : Nat) : ∀ (s : MState) (j : Nat), cx.dlen - j = m → j < cx.dlen →
    s.phase = .partData (.idx j) →
    (feed cx s ((D cx).drop j)).phase = .partData .afterD ∧
      (feed cx s ((D cx).drop j)).data = s.data ∧ (feed cx s ((D cx).drop j)).headers = s.headers ∧
      (feed cx s ((D cx).drop j)).parts = s.parts := by
  induction m with
  | zero => intro s j hm hj; omega
  | succ m ih =>
    intro s j hm hj hp
    have hjD : j < (D cx).length := by rw [← dlen_eq]; exact hj
    rw [D_drop_cons cx j hjD]
    simp only [feed, List.foldl_cons]
    have hd : (D cx)[j] = cx.dAt j := (dAt_eq cx j hj).symm
    by_cases hlast : j + 1 = cx.dlen
    · have hs : step cx s ((D cx)[j]) = { s with pos := s.pos + 1, phase := .partData .afterD } := by
        simp [step, hp, matchByte, hd, hlast]
      rw [hs]
      have : (D cx).drop (j + 1) = [] := by simp; rw [← dlen_eq]; omega
      rw [this]; simp
    · have hs : step cx s ((D cx)[j]) = { s with pos := s.pos + 1, phase := .partData (.idx (j + 1)) } := by
        simp [step, hp, matchByte, hd, hlast]
      rw [hs]
      have := ih { s with pos := s.pos + 1, phase := .partData (.idx (j + 1)) } (j + 1) (by omega) (by omega) rfl
      simp only [feed] at this
      exact this

/-- The delimiter, read after a body: the partial match becomes data and
the delimiter is recognised. -/
theorem feed_delim (s : MState) (k : Nat) (hp : s.phase = .partData (.idx k)) (hk : k < cx.dlen) :
    (feed cx s (D cx)).phase = .partData .afterD ∧
      (feed cx s (D cx)).data.toList = s.data.toList ++ (D cx).take k ∧
      (feed cx s (D cx)).headers = s.headers ∧ (feed cx s (D cx)).parts = s.parts := by
  have h5 := dlen_ge cx
  by_cases hk0 : k = 0
  · subst hk0
    have := feed_matchFrom cx _ s 0 rfl (by omega) hp
    simp only [List.drop_zero] at this
    exact ⟨this.1, by rw [this.2.1]; simp, this.2.2⟩
  · have hDc : D cx = Byte.CR :: (D cx).drop 1 := by simp [Boundary.delimL]
    rw [hDc]
    simp only [feed, List.foldl_cons]
    have hne : Byte.CR ≠ cx.dAt k := fun h => dAt_ne_CR cx k (by omega) hk h.symm
    have hs : step cx s Byte.CR = { s with pos := s.pos + 1, phase := .partData (.idx 1), data := s.data ++ cx.delim.extract 0 k } := by
      simp [step, hp, matchByte, hne, restart] <;> (try (intro h; subst h; simp [ByteArray.extract_same]))
    rw [hs]
    have := feed_matchFrom cx _ { s with pos := s.pos + 1, phase := .partData (.idx 1), data := s.data ++ cx.delim.extract 0 k } 1 rfl (by omega) rfl
    simp only [feed] at this
    refine ⟨this.1, ?_, this.2.2⟩
    rw [this.2.1]; simp [delim_toList]
    rw [show Byte.CR :: (D cx).tail = D cx by simp [Boundary.delimL]]

/-- After the delimiter, `CR LF` ends the part and begins the next. -/
theorem feed_afterD_next (s : MState) (hp : s.phase = .partData .afterD) :
    feed cx s [Byte.CR, Byte.LF] = beginPart (finishPart { s with pos := s.pos + 2 }) := by
  cases s; simp_all [feed, step, matchByte, beginPart, finishPart]

/-- After the delimiter, `--` ends the part and the message. -/
theorem feed_afterD_last (s : MState) (hp : s.phase = .partData .afterD) :
    feed cx s [Byte.HYPHEN, Byte.HYPHEN] = { finishPart { s with pos := s.pos + 2 } with phase := .done } := by
  cases s; simp_all [feed, step, matchByte, finishPart]


/-! ## Whole parts and messages -/

/-- At the start of a part's headers, with `P` read before. -/
def PartStart (P : List RawPart) (s : MState) : Prop :=
  HdrStart s ∧ s.hdrCount = 0 ∧ s.headers = #[] ∧ s.parts.toList = P

theorem partStart_beginPart (s : MState) : PartStart s.parts.toList (beginPart s) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- A part's headers, empty line and body, then the delimiter. -/
theorem feed_part (P : List RawPart) (s : MState) (hs : PartStart P s) (p : RawPart) (hw : WFPart cx p) :
    (feed cx s (partL p ++ D cx)).phase = .partData .afterD ∧
      (feed cx s (partL p ++ D cx)).headers.toList = p.headers ∧
      (feed cx s (partL p ++ D cx)).data.toList = p.body.data.toList ∧
      (feed cx s (partL p ++ D cx)).parts.toList = P := by
  obtain ⟨hst, hc0, hh0, hP⟩ := hs
  obtain ⟨hcount, hwh, hbody⟩ := hw
  unfold partL
  rw [feed_append, feed_append, feed_append,
    feed_headers cx p.headers s hst (by omega) hwh]
  obtain ⟨h1, h2, h3, h4⟩ := hst
  have hT1 : HdrStart { s with pos := s.pos + (p.headers.flatMap headerLineL).length, hdrCount := s.hdrCount + p.headers.length, headers := s.headers ++ p.headers.toArray } := ⟨h1, h2, h3, h4⟩
  have hH1 : ({ s with pos := s.pos + (p.headers.flatMap headerLineL).length, hdrCount := s.hdrCount + p.headers.length, headers := s.headers ++ p.headers.toArray } : MState).headers.toList = p.headers := by
    simp [hh0]
  have hP1 : ({ s with pos := s.pos + (p.headers.flatMap headerLineL).length, hdrCount := s.hdrCount + p.headers.length, headers := s.headers ++ p.headers.toArray } : MState).parts.toList = P := hP
  generalize ({ s with pos := s.pos + (p.headers.flatMap headerLineL).length, hdrCount := s.hdrCount + p.headers.length, headers := s.headers ++ p.headers.toArray } : MState) = t1 at hT1 hH1 hP1 ⊢
  rw [feed_headersEnd cx t1 hT1]
  obtain ⟨k', b1, b2, b3, b4, b5⟩ := feed_body cx p.body.data.toList { t1 with pos := t1.pos + 2, phase := .partData (.idx 0), data := ByteArray.empty }
    0 rfl (by have := dlen_ge cx; omega) (by simpa using hbody)
  obtain ⟨d1, d2, d3, d4⟩ := feed_delim cx _ k' b1 b2
  refine ⟨d1, ?_, ?_, ?_⟩
  · rw [d3, b4]; exact hH1
  · rw [d2, b3]; simp
  · rw [d4, b5]; exact hP1

theorem finishPart_parts (t : MState) (p : RawPart) (P : List RawPart)
    (hh : t.headers.toList = p.headers) (hd : t.data.toList = p.body.data.toList) (hP : t.parts.toList = P) :
    (finishPart t).parts.toList = P ++ [p] := by
  simp only [finishPart, Array.toList_push, hP, hh]
  congr 2
  cases p; simp only [RawPart.mk.injEq, true_and]
  apply ByteArray.ext; apply Array.ext'; simpa using hd

/-! ## The message, as an instance of the codec theory -/

/-- After a part and its delimiter: closing the part gives `ys`. -/
def AfterPart (ys : List RawPart) (s : MState) : Prop :=
  s.phase = .partData .afterD ∧ (finishPart s).parts.toList = ys

/-- The closing delimiter has been read; the parts are `ys`. -/
def Done (ys : List RawPart) (s : MState) : Prop := s.phase = .done ∧ s.parts.toList = ys

/-- A part and the delimiter after it. -/
theorem reads_part (p : RawPart) (hw : WFPart cx p) (P : List RawPart) :
    Reads (machine cx) (PartStart P) (partL p ++ D cx) (AfterPart (P ++ [p])) := by
  intro s hs
  obtain ⟨h1, h2, h3, h4⟩ := feed_part cx P s hs p hw
  exact ⟨h1, finishPart_parts _ p P h2 h3 h4⟩

/-- `CR LF` after a delimiter begins the next part. -/
theorem reads_next (ys : List RawPart) : Reads (machine cx) (AfterPart ys) [Byte.CR, Byte.LF] (PartStart ys) := by
  intro s ⟨hp, hy⟩
  show PartStart ys (feed cx s _)
  rw [feed_afterD_next cx s hp]
  have := partStart_beginPart (finishPart { s with pos := s.pos + 2 })
  simpa [finishPart] using (show (finishPart { s with pos := s.pos + 2 }).parts.toList = ys by
    simpa [finishPart] using hy) ▸ this

/-- `--` after a delimiter ends the message. -/
theorem reads_last (ys : List RawPart) : Reads (machine cx) (AfterPart ys) [Byte.HYPHEN, Byte.HYPHEN] (Done ys) := by
  intro s ⟨hp, hy⟩
  show Done ys (feed cx s _)
  rw [feed_afterD_last cx s hp]
  exact ⟨rfl, by simpa [finishPart] using hy⟩

/-- The epilogue is ignored. -/
theorem reads_epilogue (ys : List RawPart) (l : Bytes) : Reads (machine cx) (Done ys) l (Done ys) := by
  intro s ⟨hp, hy⟩
  obtain ⟨h1, h2⟩ := feed_done cx s hp l
  exact ⟨h1, by rw [← hy]; exact congrArg _ h2⟩

/-- The opening `--boundary CR LF`. -/
theorem reads_open : Reads (machine cx) (· = {}) ((D cx).drop 2 ++ [Byte.CR, Byte.LF]) (PartStart []) := by
  intro s hs; subst hs
  show PartStart [] (feed cx {} _)
  rw [feed_open cx {} rfl]
  exact partStart_beginPart _

/-- The empty message `--boundary--`. -/
theorem reads_open_empty : Reads (machine cx) (· = {}) ((D cx).drop 2 ++ [Byte.HYPHEN, Byte.HYPHEN]) (Done []) := by
  intro s hs; subst hs
  obtain ⟨h1, h2⟩ := feed_open_empty cx {} rfl
  exact ⟨h1, by show (feed cx {} _).parts.toList = []; rw [h2]⟩

/-- Reading the whole message. -/
theorem reads_message (ps : List RawPart) (hw : ∀ p ∈ ps, WFPart cx p) (epi : Bytes) :
    Reads (machine cx) (· = {}) (printL cx.boundary ps ++ epi) (Done ps) := by
  cases ps with
  | nil =>
    rw [printL, List.append_assoc]
    exact reads_open_empty cx |>.append (reads_epilogue cx [] _)
  | cons p rest =>
    have e : printL cx.boundary (p :: rest) ++ epi =
        ((D cx).drop 2 ++ [Byte.CR, Byte.LF]) ++
          (((partL p ++ D cx) ++ rest.flatMap (fun q => [Byte.CR, Byte.LF] ++ (partL q ++ D cx))) ++
            ([Byte.HYPHEN, Byte.HYPHEN] ++ ([Byte.CR, Byte.LF] ++ epi))) := by
      simp only [printL, List.append_assoc]
    rw [e]
    have hparts := Reads.sepBy (I := PartStart) (J := AfterPart) (fun q => partL q ++ D cx)
      [Byte.CR, Byte.LF] p rest (fun acc x hx => reads_part cx x (hw x hx) acc) (reads_next cx) []
    simp only [List.nil_append] at hparts
    exact (reads_open cx).append (hparts.append ((reads_last cx _).append (reads_epilogue cx _ _)))

/-- **The multipart round trip.** Printed well-formed parts, followed by any
epilogue, parse back to exactly those parts. `WFPart` is what the printer
needs: no body contains the delimiter `CR LF -- boundary`, header names are
tokens, values contain no `CR` and do not start with a space, and headers
are within the configured limits; `Fits` is the `maxSize` limit. -/
theorem multipart_parse_print_ext (ps : List RawPart) (epi : ByteArray) (hw : ∀ p ∈ ps, WFPart cx p)
    (hf : Fits cx ps) : (parse cx (print cx.boundary ps ++ epi)).toExcept = .ok ps := by
  rw [parse_eq]
  have e : (print cx.boundary ps ++ epi).data.toList = printL cx.boundary ps ++ epi.data.toList := by
    simp [print, ByteArray.data_append]
  rw [e]
  -- truncation at `maxSize` keeps the whole message
  obtain ⟨epi', he⟩ : ∃ epi', feedT cx {} (printL cx.boundary ps ++ epi.data.toList) =
      feed cx {} (printL cx.boundary ps ++ epi') := by
    unfold feedT room
    cases hm : cx.cfg.maxSize with
    | none =>
      refine ⟨epi.data.toList, ?_⟩
      simp only
      first | rfl | rw [List.take_of_length_le (Nat.le_refl _)]
    | some m =>
      have := hf m hm
      refine ⟨epi.data.toList.take (min ((printL cx.boundary ps) ++ epi.data.toList).length (m - 0) -
        (printL cx.boundary ps).length), ?_⟩
      simp only [List.take_append]
      rw [List.take_of_length_le (by simp; omega)]
  have hd' := reads_message cx ps hw epi' {} rfl
  simp only [parseL, result, MultipartResult.toExcept, he]
  have h1 : (feed cx {} (printL cx.boundary ps ++ epi')).phase = .done := hd'.1
  have h2 : (feed cx {} (printL cx.boundary ps ++ epi')).parts.toList = ps := hd'.2
  rw [h1, h2]

end Mp
end LeanMultipart
