import LeanMultipart.RepoImpl.Querystring
import LeanMultipart.Proofs.Percent
import LeanMultipart.Theory.Codec

/-!
# The querystring state machine: proofs

* `Qs.feed_append`, `Qs.feedT_append`: feeding chunks one after another is
  feeding their concatenation, with or without `maxSize` truncation. So the
  streaming parser fed any chunking of an input gives the same fields as the
  whole-buffer parser (`Qs.parse_chunks`).
* `urldecode_urlencode`: the parser (strict or not) reads back exactly the
  pairs `urlencode` printed, and `urlencode_urldecode_ext` the same on any
  continuation after a `&`.
* `Qs.parse_total`: the parser processes `min(len, maxSize)` bytes and every
  error offset lies within them.
-/

namespace LeanMultipart
namespace Qs

/-! ## Chunking -/

@[simp] theorem step_pos (cfg : QsConfig) (s : QsState) (c : UInt8) :
    (step cfg s c).pos = s.pos + 1 := by
  unfold step
  cases s.phase <;> simp only [nameByte, finishField] <;> split <;> (try split) <;> (try split) <;> rfl

theorem counts (cfg : QsConfig) : (machine cfg).Counts := step_pos cfg

theorem feed_append (cfg : QsConfig) (s : QsState) (a b : Bytes) :
    feed cfg s (a ++ b) = feed cfg (feed cfg s a) b := (machine cfg).feed_append s a b

theorem feed_pos (cfg : QsConfig) (s : QsState) (l : Bytes) :
    (feed cfg s l).pos = s.pos + l.length := (machine cfg).feed_pos (counts cfg) s l

theorem feedT_append (cfg : QsConfig) (s : QsState) (a b : Bytes) :
    feedT cfg (feedT cfg s a) b = feedT cfg s (a ++ b) := (machine cfg).feedT_append ((machine cfg).chunkable_of_counts (counts cfg)) s a b

@[simp] theorem feedT_nil (cfg : QsConfig) (s : QsState) : feedT cfg s [] = s := (machine cfg).feedT_nil s

theorem feedChunks_eq (cfg : QsConfig) (s : QsState) (cs : List Bytes) :
    feedChunks cfg s cs = feedT cfg s cs.flatten := (machine cfg).feedChunks_eq ((machine cfg).chunkable_of_counts (counts cfg)) s cs

theorem feedA_eq (cfg : QsConfig) (s : QsState) (b : ByteArray) : feedA cfg s b = feedT cfg s b.data.toList :=
  (machine cfg).feedA_eq s b

theorem parse_eq (cfg : QsConfig) (b : ByteArray) : parse cfg b = parseL cfg b.data.toList := by
  simp [parse, parseL, feedA_eq]

/-- Streaming equals whole-buffer: any chunking gives the same result. -/
theorem parse_chunks (cfg : QsConfig) (cs : List Bytes) :
    result (feedChunks cfg {} cs) = parseL cfg cs.flatten := by
  rw [feedChunks_eq]; rfl

/-! ## Totality and error localisation -/

/-- The invariant behind error localisation. -/
def ErrInv (s : QsState) : Prop :=
  s.nameStart ≤ s.pos ∧ ∀ e, s.phase = .failed e → e.offset < s.pos

theorem step_errInv (cfg : QsConfig) (s : QsState) (c : UInt8) (h : ErrInv s) :
    ErrInv (step cfg s c) := by
  obtain ⟨h1, h2⟩ := h
  unfold ErrInv step
  cases hp : s.phase with
  | failed e0 => have := h2 e0 hp; simp only ; exact ⟨by omega, fun e he => by cases he; omega⟩
  | beforeField fs =>
    simp only [nameByte, finishField]
    repeat' split
    all_goals
      refine ⟨(by simp <;> omega), ?_⟩
      intro e he
      simp at he
      try subst he
      try simp_all
      try omega
  | fieldName =>
    simp only [nameByte, finishField]
    repeat' split
    all_goals
      refine ⟨(by simp <;> omega), ?_⟩
      intro e he
      simp at he
      try subst he
      try simp_all
      try omega
  | fieldData =>
    simp only [finishField]
    repeat' split
    all_goals
      refine ⟨(by simp <;> omega), ?_⟩
      intro e he
      simp at he
      try subst he
      try simp_all
      try omega

theorem feed_errInv (cfg : QsConfig) (s : QsState) (l : Bytes) (h : ErrInv s) :
    ErrInv (feed cfg s l) := by
  induction l generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_errInv cfg s c h)

theorem finish_failed {s : QsState} {e : QsError} (h : (finish s).phase = .failed e) :
    s.phase = .failed e := by
  unfold finish at h; split at h <;> simp_all 

/-- Totality: the parser consumes exactly `min(len, maxSize)` bytes, and an
error's offset is one of them. -/
theorem parse_total (cfg : QsConfig) (l : Bytes) :
    processed cfg l = room cfg {} l.length ∧
    ∀ e, parseL cfg l = .error e → e.offset < processed cfg l := by
  refine ⟨?_, ?_⟩
  · simp only [processed, feedT, feed_pos, List.length_take]
    unfold room; split <;> simp <;> omega
  · intro e he
    have hi := (feed_errInv cfg {} (l.take (room cfg {} l.length))
      ⟨Nat.le_refl _, fun e h => by simp at h⟩).2
    simp only [parseL, result] at he
    split at he
    · rename_i e' hph
      cases he
      exact hi e (finish_failed hph)
    · cases he

/-! ## The round trip -/

/-- Name bytes that contain neither `=` nor `&` accumulate. -/
theorem feed_nameChars (cfg : QsConfig) (s : QsState) (l : Bytes)
    (hp : s.phase = .fieldName) (hl : ∀ c ∈ l, c ≠ Byte.AMP ∧ c ≠ Byte.EQ) :
    (feed cfg s l).phase = .fieldName ∧ (feed cfg s l).name.toList = s.name.toList ++ l ∧
      (feed cfg s l).value = s.value ∧ (feed cfg s l).fields = s.fields := by
  induction l generalizing s with
  | nil => simp [feed, hp]
  | cons c cs ih =>
    have hc := hl c (by simp)
    have hs : step cfg s c = { s with pos := s.pos + 1, phase := .fieldName, name := s.name.push c } := by
      simp [step, hp, nameByte, hc.1, hc.2]
    simp only [feed, List.foldl_cons] at ih ⊢
    rw [hs]
    have := ih { s with pos := s.pos + 1, phase := .fieldName, name := s.name.push c } rfl
      (fun x hx => hl x (by simp [hx]))
    simp only [ByteArray.toList_eq, ByteArray.data_push, Array.toList_push, List.append_assoc,
      List.singleton_append] at this ⊢
    exact this

/-- Value bytes that contain no `&` accumulate. -/
theorem feed_dataChars (cfg : QsConfig) (s : QsState) (l : Bytes)
    (hp : s.phase = .fieldData) (hl : ∀ c ∈ l, c ≠ Byte.AMP) :
    (feed cfg s l).phase = .fieldData ∧ (feed cfg s l).value.toList = s.value.toList ++ l ∧
      (feed cfg s l).name = s.name ∧ (feed cfg s l).fields = s.fields := by
  induction l generalizing s with
  | nil => simp [feed, hp]
  | cons c cs ih =>
    have hc := hl c (by simp)
    have hs : step cfg s c = { s with pos := s.pos + 1, value := s.value.push c } := by
      simp [step, hp, hc]
    simp only [feed, List.foldl_cons] at ih ⊢
    rw [hs]
    have := ih { s with pos := s.pos + 1, value := s.value.push c } hp (fun x hx => hl x (by simp [hx]))
    simp only [ByteArray.toList_eq, ByteArray.data_push, Array.toList_push, List.append_assoc,
      List.singleton_append] at this ⊢
    exact this

/-- The raw field a printed pair parses to. -/
def encField (p : Bytes × Bytes) : QsField := (⟨(quotePlusL p.1).toArray⟩, ⟨(quotePlusL p.2).toArray⟩)

/-- One printed pair, read from between fields, leaves the parser inside its
value with the pair's name and value buffered. -/
theorem feed_encodePair (cfg : QsConfig) (s : QsState) (fs : Bool) (p : Bytes × Bytes)
    (hp : s.phase = .beforeField fs) :
    (feed cfg s (encodePairL p)).phase = .fieldData ∧
      (feed cfg s (encodePairL p)).name.toList = quotePlusL p.1 ∧
      (feed cfg s (encodePairL p)).value.toList = quotePlusL p.2 ∧
      (feed cfg s (encodePairL p)).fields = s.fields := by
  have hn := quotePlusL_no_sep p.1
  have hv := quotePlusL_no_sep p.2
  unfold encodePairL
  -- the state after the name and `=`
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5⟩ : ∃ t, feed cfg s (quotePlusL p.1 ++ [Byte.EQ]) = t ∧
      t.phase = .fieldData ∧ t.name.toList = quotePlusL p.1 ∧ t.value = ByteArray.empty ∧ t.fields = s.fields := by
    cases hq : quotePlusL p.1 with
    | nil =>
      refine ⟨_, rfl, ?_⟩
      simp [feed, step, hp, nameByte, show Byte.EQ ≠ Byte.AMP by decide]
    | cons c cs =>
      rw [hq] at hn
      have hc := hn c (by simp)
      have hs : step cfg s c = { s with pos := s.pos + 1, nameStart := s.pos, value := ByteArray.empty, phase := .fieldName, name := ByteArray.empty.push c } := by
        simp [step, hp, nameByte, hc.1, hc.2]
      refine ⟨_, rfl, ?_⟩
      simp only [feed, List.cons_append, List.foldl_cons, hs, List.foldl_append] at ⊢
      have hm := feed_nameChars cfg { s with pos := s.pos + 1, nameStart := s.pos, value := ByteArray.empty, phase := .fieldName, name := ByteArray.empty.push c } cs rfl (fun x hx => hn x (by simp [hx]))
      simp only [feed] at hm
      generalize List.foldl (step cfg) _ cs = u at hm ⊢
      obtain ⟨h1, h2, h3, h4⟩ := hm
      have hu : step cfg u Byte.EQ = { u with pos := u.pos + 1, phase := .fieldData } := by
        simp [step, h1, nameByte]
      simp only [List.foldl_nil, hu]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all
  rw [feed_append, ht1]
  have := feed_dataChars cfg t (quotePlusL p.2) ht2 (fun x hx => (hv x hx).1)
  rw [ht4] at this
  simp only [ByteArray.toList_eq, ByteArray.data_empty', Array.toList_empty, List.nil_append] at this
  exact ⟨this.1, this.2.2.1 ▸ ht3, by simpa using this.2.1, this.2.2.2.trans ht5⟩

theorem array_eq_of_toList {a : ByteArray} {l : Bytes} (h : a.toList = l) : a = ⟨l.toArray⟩ := by
  apply ByteArray.ext; rw [← h]; simp

/-! ## The urlencoded codec, as an instance of the codec theory -/

/-- Between fields, with the pairs `acc` read. -/
def Between (acc : List (Bytes × Bytes)) (s : QsState) : Prop :=
  (∃ b, s.phase = .beforeField b) ∧ s.fields.toList = acc.map encField ∧ s.name = ByteArray.empty ∧ s.value = ByteArray.empty

/-- Inside the value of the last pair of `acc`. -/
def InPair (acc : List (Bytes × Bytes)) (s : QsState) : Prop :=
  s.phase = .fieldData ∧ (finishField s).fields.toList = acc.map encField

theorem reads_pair (cfg : QsConfig) (acc : List (Bytes × Bytes)) (x : Bytes × Bytes) :
    Reads (machine cfg) (Between acc) (encodePairL x) (InPair (acc ++ [x])) := by
  intro s ⟨⟨b, hb⟩, hf, _, _⟩
  obtain ⟨h1, h2, h3, h4⟩ := feed_encodePair cfg s b x hb
  refine ⟨h1, ?_⟩
  show (finishField (feed cfg s _)).fields.toList = _
  simp [finishField, Array.toList_push, h4, hf, encField, array_eq_of_toList h2, array_eq_of_toList h3]

theorem reads_amp (cfg : QsConfig) (ys : List (Bytes × Bytes)) :
    Reads (machine cfg) (InPair ys) [Byte.AMP] (Between ys) := by
  intro s ⟨hp, hf⟩
  show Between ys (feed cfg s _)
  have : feed cfg s [Byte.AMP] = { finishField s with pos := s.pos + 1, phase := .beforeField true } := by
    simp [feed, step, hp, finishField]
  rw [this]
  exact ⟨⟨true, rfl⟩, hf, rfl, rfl⟩

theorem reads_urlencode (cfg : QsConfig) (ps : List (Bytes × Bytes)) :
    Reads (machine cfg) (Between []) (urlencodeL ps) (fun s => result s = .ok (ps.map encField)) := by
  cases ps with
  | nil =>
    intro s ⟨⟨b, hb⟩, hf, _, _⟩
    simpa [urlencodeL, Machine.feed, result, finish, hb] using hf
  | cons p rest =>
    have h := Reads.sepBy (I := Between) (J := InPair) encodePairL [Byte.AMP] p rest
      (fun acc x _ => reads_pair cfg acc x) (reads_amp cfg) []
    simp only [List.nil_append] at h
    refine Reads.mono (fun _ h => h) ?_ h
    intro s ⟨hp, hf⟩
    simp [result, finish, hp, hf]

/-- `room` is everything when there is no limit or the input fits. -/
def Fits (cfg : QsConfig) (n : Nat) : Prop := ∀ m, cfg.maxSize = some m → n ≤ m

theorem feedT_fits (cfg : QsConfig) (l : Bytes) (h : Fits cfg l.length) :
    feedT cfg {} l = feed cfg {} l := by
  unfold feedT room
  cases hm : cfg.maxSize with
  | none => simp
  | some m => have := h m hm; simp only; rw [List.take_of_length_le (by simp; omega)]

/-- The parser, strict or not, reads back the raw (still encoded) pairs. -/
theorem parse_urlencode (cfg : QsConfig) (ps : List (Bytes × Bytes))
    (h : Fits cfg (urlencodeL ps).length) :
    parseL cfg (urlencodeL ps) = .ok (ps.map encField) := by
  rw [parseL, feedT_fits cfg _ h]
  exact reads_urlencode cfg ps {} ⟨⟨false, rfl⟩, rfl, rfl, rfl⟩

/-- The urlencoded round trip: decoding what `urlencode` printed gives back
the pairs. -/
theorem urldecode_urlencode (ps : List (Bytes × Bytes)) : urldecodeL (urlencodeL ps) = ps := by
  unfold urldecodeL
  rw [parse_urlencode {} ps (fun m h => by cases h)]
  simp only [List.map_map]
  conv => rhs; rw [← List.map_id ps]
  apply List.map_congr_left
  intro p _
  simp [encField, unquotePlus_quotePlus]

/-! ## The frame: what was read before does not change what comes next -/

/-- Phases equal up to upstream's `_found_sep` flag. -/
def phaseNorm : QsPhase → QsPhase
  | .beforeField _ => .beforeField false
  | p => p

/-- `s` is `t` with `F` read before, up to the separator flag. -/
def Frame (F : List QsField) (s t : QsState) : Prop :=
  phaseNorm s.phase = phaseNorm t.phase ∧ s.name = t.name ∧ s.value = t.value ∧
    s.fields.toList = F ++ t.fields.toList

theorem step_frame (cfg : QsConfig) (hs : cfg.strictParsing = false) (F : List QsField) (s t : QsState)
    (c : UInt8) (h : Frame F s t) : Frame F (step cfg s c) (step cfg t c) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold step
  cases hp : s.phase <;> cases hq : t.phase <;> simp [phaseNorm, hp, hq] at h1 <;>
    simp only [nameByte, finishField, hs] <;> (repeat' split) <;>
    simp_all [Frame, phaseNorm, Array.toList_push]

theorem feed_frame (cfg : QsConfig) (hs : cfg.strictParsing = false) (F : List QsField) (s t : QsState)
    (l : Bytes) (h : Frame F s t) : Frame F (feed cfg s l) (feed cfg t l) := by
  induction l generalizing s t with
  | nil => exact h
  | cons c cs ih => exact ih _ _ (step_frame cfg hs F s t c h)

theorem result_frame (F : List QsField) (s t : QsState) (h : Frame F s t) :
    result s = (result t).map (F ++ ·) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold result finish
  cases hp : s.phase <;> cases hq : t.phase <;> simp [phaseNorm, hp, hq] at h1 <;>
    simp_all [finishField, Array.toList_push, Except.map]

theorem step_nonstrict (cfg : QsConfig) (hs : cfg.strictParsing = false) (s : QsState) (c : UInt8)
    (h : ∀ e, s.phase ≠ .failed e) : ∀ e, (step cfg s c).phase ≠ .failed e := by
  intro e
  unfold step
  cases hp : s.phase <;> simp only [nameByte, finishField, hs] <;> (repeat' split) <;> simp_all

theorem feed_nonstrict (cfg : QsConfig) (hs : cfg.strictParsing = false) (s : QsState) (l : Bytes)
    (h : ∀ e, s.phase ≠ .failed e) : ∀ e, (feed cfg s l).phase ≠ .failed e := by
  induction l generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_nonstrict cfg hs s c h)

/-- The non-strict parser never fails. -/
theorem result_nonstrict (cfg : QsConfig) (_hs : cfg.strictParsing = false) (s : QsState)
    (h : ∀ e, s.phase ≠ .failed e) : ∀ e, result s ≠ .error e := by
  intro e he
  unfold result at he
  split at he
  · rename_i e' hph; exact h e' (finish_failed hph)
  · cases he

/-- The `_ext` form of the urlencoded round trip: the pairs printed, a `&`,
then any continuation, decode to the pairs followed by the continuation's
own decoding (non-strict, as Starlette uses it). -/
theorem urlencode_urldecode_ext (ps : List (Bytes × Bytes)) (rest : Bytes) :
    urldecodeL (urlencodeL ps ++ [Byte.AMP] ++ rest) = ps ++ urldecodeL rest := by
  -- the state after the pairs and the `&`
  obtain ⟨s1, hs1, ⟨⟨b, hp1⟩, hf1, hn1, hv1⟩⟩ : ∃ s1, feed {} {} (urlencodeL ps ++ [Byte.AMP]) = s1 ∧
      Between ps s1 := by
    refine ⟨_, rfl, ?_⟩
    have h0 : Between [] ({} : QsState) := ⟨⟨false, rfl⟩, rfl, rfl, rfl⟩
    cases ps with
    | nil =>
      show Between [] (step {} {} Byte.AMP)
      exact ⟨⟨true, rfl⟩, rfl, rfl, rfl⟩
    | cons p rest =>
      have h := Reads.sepBy (I := Between) (J := InPair) encodePairL [Byte.AMP] p rest
        (fun acc x _ => reads_pair {} acc x) (reads_amp {}) []
      simp only [List.nil_append] at h
      exact (h.append (reads_amp {} _)) {} h0
  have hfr : Frame (ps.map encField) s1 {} := ⟨by simp [hp1, phaseNorm], hn1, hv1, by simp [hf1]⟩
  unfold urldecodeL
  have e1 : parseL {} (urlencodeL ps ++ [Byte.AMP] ++ rest) = result (feed {} s1 rest) := by
    rw [parseL, feedT_fits {} _ (fun m h => by cases h), feed_append, hs1]
  have e2 : parseL {} rest = result (feed {} {} rest) := by
    rw [parseL, feedT_fits {} _ (fun m h => by cases h)]
  rw [e1, e2, result_frame _ _ _ (feed_frame {} rfl _ _ _ rest hfr)]
  cases hr : result (feed {} {} rest) with
  | error e =>
    exact absurd hr (result_nonstrict {} rfl (feed {} {} rest)
      (feed_nonstrict {} rfl {} rest (by simp)) e)
  | ok fs =>
    simp only [Except.map, List.map_append, List.map_map]
    congr 1
    conv => rhs; rw [← List.map_id ps]
    apply List.map_congr_left
    intro p _
    simp [encField, unquotePlus_quotePlus]

end Qs
end LeanMultipart
