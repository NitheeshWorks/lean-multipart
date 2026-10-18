import LeanMultipart.RepoImpl.Form
import LeanMultipart.Proofs.ByteFacts

/-!
# The Content-Disposition round trip

`Options.parseL_dispositionL`: `parse_options_header` reads back the `name`
and `filename` that `dispositionValue` printed, for names without `"`, `\`
or `;` (the bytes that the quoted-string printer does not escape; see
UP-005 for upstream's behaviour on a trailing backslash). Built from small
lemmas, one per stage of `_parseparam`: splitting at `;`, grouping by quote
parity, normalising a piece, and unquoting a value.
-/

namespace LeanMultipart
namespace Options

/-! ## Splitting at `;` -/

theorem splitSemiGo_noSemi (a : Bytes) (h : Byte.SEMI ∉ a) :
    ∀ acc, splitSemiGo acc a = [acc.reverse ++ a] := by
  induction a with
  | nil => intro acc; simp [splitSemiGo]
  | cons c cs ih =>
    intro acc
    have hc : c ≠ Byte.SEMI := fun he => h (he ▸ List.mem_cons_self ..)
    simp only [splitSemiGo, beq_iff_eq, hc, ite_false]
    rw [ih (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp

theorem splitSemiGo_append (a b : Bytes) (h : Byte.SEMI ∉ a) :
    ∀ acc, splitSemiGo acc (a ++ Byte.SEMI :: b) = (acc.reverse ++ a) :: splitSemiGo [] b := by
  induction a with
  | nil => intro acc; simp [splitSemiGo]
  | cons c cs ih =>
    intro acc
    have hc : c ≠ Byte.SEMI := fun he => h (he ▸ List.mem_cons_self ..)
    simp only [List.cons_append, splitSemiGo, beq_iff_eq, hc, ite_false]
    rw [ih (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp

/-! ## Quote parity -/

theorem quoteDiff_cons_quote (l : Bytes) : quoteDiff (Byte.DQUOTE :: l) = 1 + quoteDiff l := by
  cases l with
  | nil => rfl
  | cons d r => simp [quoteDiff]

theorem quoteDiff_cons_other (c : UInt8) (l : Bytes) (h1 : c ≠ Byte.DQUOTE) (h2 : c ≠ Byte.BSLASH) :
    quoteDiff (c :: l) = quoteDiff l := by
  cases l with
  | nil => simp [quoteDiff, h1]
  | cons d r => simp [quoteDiff, h1, h2]

theorem quoteDiff_append (a b : Bytes) (h : ∀ c ∈ a, c ≠ Byte.BSLASH) :
    quoteDiff (a ++ b) = quoteDiff a + quoteDiff b := by
  induction a with
  | nil => simp [quoteDiff]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hq : c = Byte.DQUOTE
    · subst hq; rw [List.cons_append, quoteDiff_cons_quote, quoteDiff_cons_quote, ih']; omega
    · rw [List.cons_append, quoteDiff_cons_other _ _ hq hc, quoteDiff_cons_other _ _ hq hc, ih']

theorem quoteDiff_safe (l : Bytes) (h : ∀ c ∈ l, c ≠ Byte.DQUOTE ∧ c ≠ Byte.BSLASH) : quoteDiff l = 0 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    rw [quoteDiff_cons_other _ _ hc.1 hc.2, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- With every piece's quotes balanced, grouping changes nothing. -/
theorem groupAux_even (ps : List Bytes) (hps : ∀ p ∈ ps, quoteDiff p % 2 = 0) :
    ∀ acc d, d % 2 = 0 → group.groupAux acc d ps = acc :: ps := by
  induction ps with
  | nil => intro acc d _; rfl
  | cons q qs ih =>
    intro acc d hd
    simp only [group.groupAux, hd, beq_self_eq_true, ite_true]
    rw [ih (fun p hp => hps p (List.mem_cons_of_mem _ hp)) q (quoteDiff q) (hps q (List.mem_cons_self ..))]

theorem group_even (ps : List Bytes) (hps : ∀ p ∈ ps, quoteDiff p % 2 = 0) : group ps = ps := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    exact groupAux_even ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) p _ (hps p (List.mem_cons_self ..))

/-! ## Normalising a piece -/

theorem idxOf?_append (a b : Bytes) (x : UInt8) (h : x ∉ a) : (a ++ x :: b).idxOf? x = some a.length := by
  induction a with
  | nil => simp [List.idxOf?_cons]
  | cons c cs ih =>
    have hc : c ≠ x := fun he => h (he ▸ List.mem_cons_self ..)
    rw [List.cons_append, List.idxOf?_cons, ih (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp [hc]

theorem dropWhile_rev_quote (z : Bytes) :
    ((z ++ [Byte.DQUOTE]).reverse.dropWhile Byte.isPySpace).reverse = z ++ [Byte.DQUOTE] := by
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.dropWhile_cons_of_neg (by decide)]
  simp

/-- `strip` leaves a string that starts with a non-space and ends with `"`. -/
theorem strip_of_ends (k0 : UInt8) (z : Bytes) (hk0 : Byte.isPySpace k0 = false) :
    strip (k0 :: (z ++ [Byte.DQUOTE])) = k0 :: (z ++ [Byte.DQUOTE]) := by
  unfold strip
  rw [List.dropWhile_cons_of_neg (by simp [hk0])]
  have := dropWhile_rev_quote (k0 :: z)
  simpa using this

theorem lstrip_quote (z : Bytes) : lstrip (Byte.DQUOTE :: z) = Byte.DQUOTE :: z := by
  simp [lstrip, List.dropWhile_cons_of_neg, show Byte.isPySpace Byte.DQUOTE = false by decide]

theorem take_len (a b : Bytes) : (a ++ b).take a.length = a := by simp

theorem drop_len_succ (a : Bytes) (x : UInt8) (b : Bytes) : (a ++ x :: b).drop (a.length + 1) = b := by
  induction a <;> simp_all

/-- A quoted parameter piece as the printer writes it, `␠key="v"`. -/
def pieceL (key v : Bytes) : Bytes := Byte.SPACE :: (key ++ Byte.EQ :: Byte.DQUOTE :: (v ++ [Byte.DQUOTE]))

/-- What a key must satisfy (checked by `decide` for `name` and `filename`). -/
def GoodKey (key : Bytes) : Prop :=
  Byte.EQ ∉ key ∧ key.map Byte.pyLower = key ∧ rstrip (Byte.SPACE :: key) = Byte.SPACE :: key ∧
    ∃ k0 ks, key = k0 :: ks ∧ Byte.isPySpace k0 = false

theorem goodKey_name : GoodKey (ascii "name") := by
  refine ⟨by decide, by decide, by decide, _, _, rfl, by decide⟩

theorem goodKey_filename : GoodKey (ascii "filename") := by
  refine ⟨by decide, by decide, by decide, _, _, rfl, by decide⟩

theorem normPiece_piece (key v : Bytes) (hk : GoodKey key) :
    normPiece (pieceL key v) = key ++ Byte.EQ :: Byte.DQUOTE :: (v ++ [Byte.DQUOTE]) := by
  obtain ⟨hkeq, hlower, hr, k0, ks, rfl, hk0⟩ := hk
  have hsp : Byte.EQ ∉ Byte.SPACE :: (k0 :: ks) := by
    intro hm; rcases List.mem_cons.1 hm with h | h
    · exact absurd h (by decide)
    · exact hkeq h
  have e : pieceL (k0 :: ks) v = (Byte.SPACE :: (k0 :: ks)) ++ Byte.EQ :: Byte.DQUOTE :: (v ++ [Byte.DQUOTE]) := by
    simp [pieceL]
  unfold normPiece
  rw [e, idxOf?_append _ _ _ hsp]
  simp only
  rw [take_len, drop_len_succ, hr, lstrip_quote]
  have hp : (Byte.SPACE :: (k0 :: ks)).map Byte.pyLower = Byte.SPACE :: (k0 :: ks) := by
    rw [List.map_cons, hlower]; rfl
  rw [hp]
  have e2 : Byte.SPACE :: k0 :: ks ++ [Byte.EQ] ++ Byte.DQUOTE :: (v ++ [Byte.DQUOTE]) =
      Byte.SPACE :: k0 :: ((ks ++ Byte.EQ :: Byte.DQUOTE :: v) ++ [Byte.DQUOTE]) := by simp
  rw [e2]
  unfold strip
  rw [List.dropWhile_cons_of_pos (by decide)]
  have := strip_of_ends k0 (ks ++ Byte.EQ :: Byte.DQUOTE :: v) hk0
  unfold strip at this
  rw [this]
  simp


/-! ## Unquoting and the parameter dictionary -/

theorem replace2_of_not_mem (a b new : UInt8) : ∀ (l : Bytes), a ∉ l → replace2 a b new l = l
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: rest, h => by
    have hc : c ≠ a := fun he => h (he ▸ List.mem_cons_self ..)
    have ih := replace2_of_not_mem a b new (d :: rest) (fun hm => h (List.mem_cons_of_mem _ hm))
    have hcb : (c == a) = false := by simpa using hc
    simp only [replace2, hcb, Bool.false_and, Bool.false_eq_true, ite_false, ih]

theorem unquote_quoted (v : Bytes) (hv : Byte.BSLASH ∉ v) : unquote (Byte.DQUOTE :: (v ++ [Byte.DQUOTE])) = v := by
  have hl : (Byte.DQUOTE :: (v ++ [Byte.DQUOTE])).getLast? = some Byte.DQUOTE := by
    rw [← List.cons_append, List.getLast?_append]; simp
  unfold unquote
  rw [hl]
  simp [replace2_of_not_mem _ _ _ v hv]

theorem ie6_of_no_backslash (v : Bytes) (hv : Byte.BSLASH ∉ v) : ie6 v = v := by
  unfold ie6
  have h1 : ((v.drop 1).take 2 == [Byte.COLON, Byte.BSLASH]) = false := by
    rw [beq_eq_false_iff_ne]; intro he
    have : Byte.BSLASH ∈ (v.drop 1).take 2 := by rw [he]; simp
    exact hv (List.mem_of_mem_drop (List.mem_of_mem_take this))
  have h2 : (v.take 2 == [Byte.BSLASH, Byte.BSLASH]) = false := by
    rw [beq_eq_false_iff_ne]; intro he
    have : Byte.BSLASH ∈ v.take 2 := by rw [he]; simp
    exact hv (List.mem_of_mem_take this)
  rw [h1, h2]; rfl

theorem partitionEq_piece (key v : Bytes) (hk : Byte.EQ ∉ key) :
    partitionEq (key ++ Byte.EQ :: Byte.DQUOTE :: (v ++ [Byte.DQUOTE])) = (key, Byte.DQUOTE :: (v ++ [Byte.DQUOTE])) := by
  unfold partitionEq
  rw [idxOf?_append _ _ _ hk]
  simp only
  rw [take_len, drop_len_succ]

/-! ## The printed `Content-Disposition` value -/

/-- `form-data; name="n"` and, for a file, `; filename="f"`. -/
def dispositionL (n : Bytes) (f : Option Bytes) : Bytes :=
  ascii "form-data" ++ Byte.SEMI :: (pieceL (ascii "name") n ++
    (match f with
     | none => []
     | some f => Byte.SEMI :: pieceL (ascii "filename") f))

theorem safe_noSemi {l : Bytes} (h : SafeParam l) : Byte.SEMI ∉ l := fun hm => (h _ hm).2.2 rfl
theorem safe_noBslash {l : Bytes} (h : SafeParam l) : Byte.BSLASH ∉ l := fun hm => (h _ hm).2.1 rfl

theorem pieceL_noSemi (key v : Bytes) (hk : Byte.SEMI ∉ key) (hv : SafeParam v) : Byte.SEMI ∉ pieceL key v := by
  simp only [pieceL, List.mem_cons, List.mem_append, not_or]
  refine ⟨by decide, hk, by decide, by decide, safe_noSemi hv, by simp⟩

theorem quoteDiff_pieceL (key v : Bytes) (hk : Byte.BSLASH ∉ key)
    (hpre : quoteDiff (Byte.SPACE :: (key ++ [Byte.EQ])) = 0) (hv : SafeParam v) :
    quoteDiff (pieceL key v) % 2 = 0 := by
  have hb : ∀ c ∈ Byte.SPACE :: (key ++ [Byte.EQ]), c ≠ Byte.BSLASH := by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · decide
    · rcases List.mem_append.1 hc with hc | hc
      · exact fun he => hk (he ▸ hc)
      · rw [List.mem_singleton.1 hc]; decide
  have e : pieceL key v = (Byte.SPACE :: (key ++ [Byte.EQ])) ++ Byte.DQUOTE :: (v ++ [Byte.DQUOTE]) := by
    simp [pieceL]
  rw [e, quoteDiff_append _ _ hb, quoteDiff_cons_quote,
    quoteDiff_append _ _ (fun c hc => (hv c hc).2.1), quoteDiff_safe v (fun c hc => ⟨(hv c hc).1, (hv c hc).2.1⟩), hpre]
  simp [quoteDiff]

theorem split_dispositionL (n : Bytes) (f : Option Bytes) (hn : SafeParam n)
    (hf : ∀ x, f = some x → SafeParam x) :
    splitSemi (dispositionL n f) =
      ascii "form-data" :: pieceL (ascii "name") n :: f.toList.map (pieceL (ascii "filename")) := by
  unfold splitSemi dispositionL
  rw [splitSemiGo_append _ _ (by decide)]
  simp only [List.reverse_nil, List.nil_append]
  congr 1
  cases f with
  | none =>
    simp only [List.append_nil]
    rw [splitSemiGo_noSemi _ (pieceL_noSemi _ _ (by decide) hn)]; rfl
  | some x =>
    rw [splitSemiGo_append _ _ (pieceL_noSemi _ _ (by decide) hn),
      splitSemiGo_noSemi _ (pieceL_noSemi _ _ (by decide) (hf x rfl))]
    rfl

theorem normPiece_formData : normPiece (ascii "form-data") = ascii "form-data" := by decide

/-- `parse_options_header` reads back the printed `Content-Disposition`. -/
theorem parseL_dispositionL (n : Bytes) (f : Option Bytes) (hn : SafeParam n)
    (hf : ∀ x, f = some x → SafeParam x) :
    parseL (dispositionL n f) =
      (ascii "form-data", (ascii "name", n) :: f.toList.map (fun x => (ascii "filename", x))) := by
  have hne : (dispositionL n f).isEmpty = false := by simp [dispositionL, ascii]
  have hsemi : (dispositionL n f).contains Byte.SEMI = true := by
    simp [dispositionL]
  have hpp : parseParam (dispositionL n f) =
      ascii "form-data" :: (ascii "name" ++ Byte.EQ :: Byte.DQUOTE :: (n ++ [Byte.DQUOTE])) ::
        f.toList.map (fun x => ascii "filename" ++ Byte.EQ :: Byte.DQUOTE :: (x ++ [Byte.DQUOTE])) := by
    unfold parseParam
    rw [split_dispositionL n f hn hf, group_even]
    · simp only [List.map_cons, List.map_map, normPiece_formData, normPiece_piece _ _ goodKey_name]
      congr 2
      apply List.map_congr_left
      intro x _
      exact normPiece_piece _ _ goodKey_filename
    · intro p hp
      simp only [List.mem_cons, List.mem_map, Option.mem_toList] at hp
      rcases hp with rfl | rfl | ⟨x, hx, rfl⟩
      · decide
      · exact quoteDiff_pieceL _ _ (by decide) (by decide) hn
      · exact quoteDiff_pieceL _ _ (by decide) (by decide) (hf x hx)
  unfold parseL
  rw [hne, hsemi, hpp]
  simp only [Bool.false_eq_true, ite_false, Bool.not_true]
  unfold addParams
  rw [partitionEq_piece _ _ goodKey_name.1]
  simp only [show (ascii "name").contains 42 = false by decide, Bool.false_eq_true, ite_false,
    unquote_quoted n (safe_noBslash hn), show (ascii "name" == ascii "filename") = false by decide]
  cases f with
  | none => rfl
  | some x =>
    simp only [Option.toList_some, List.map_cons, List.map_nil]
    unfold addParams
    rw [partitionEq_piece _ _ goodKey_filename.1]
    simp only [show (ascii "filename").contains 42 = false by decide, Bool.false_eq_true, ite_false,
      unquote_quoted x (safe_noBslash (hf x rfl)), beq_self_eq_true, ite_true,
      ie6_of_no_backslash x (safe_noBslash (hf x rfl))]
    simp [addParams, dictSet, show (ascii "name" == ascii "filename") = false by decide]

end Options

theorem dispositionValue_toList (n : ByteArray) (f : Option ByteArray) :
    (dispositionValue n f).data.toList = Options.dispositionL n.data.toList (f.map (·.data.toList)) := by
  cases f <;> simp [dispositionValue, Options.dispositionL, Options.pieceL, ByteArray.data_append, ascii] <;> decide

theorem lookup_ok (l : List (Bytes × Bytes)) (k : Bytes) (v : Bytes) (h : l.find? (fun p => p.1 == k) = some (k, v)) :
    Options.lookup l k = some v := by simp [Options.lookup, h]

/-- **The Content-Disposition round trip.** The `name` and `filename` a form
part was printed with are read back by upstream's `parse_options_header`
logic, for names without `"`, `\` or `;`. -/
theorem dispositionParams_formPart (n : ByteArray) (f ct : Option ByteArray) (body : ByteArray)
    (hn : Options.SafeParam n.data.toList) (hf : ∀ x, f = some x → Options.SafeParam x.data.toList) :
    dispositionParams (formPart n f ct body).headers = (some n.data.toList, f.map (·.data.toList)) := by
  have hcd : headerLookup (formPart n f ct body).headers (ascii "content-disposition") = some (dispositionValue n f) := by
    cases ct <;> simp [formPart, headerLookup, lowerAscii, ascii] <;> decide
  unfold dispositionParams
  rw [hcd]
  simp only [Option.getD_some, dispositionValue_toList]
  rw [Options.parseL_dispositionL _ _ hn (fun x hx => by
    cases f with
    | none => cases hx
    | some y => simp at hx; subst hx; exact hf y rfl)]
  have hnf : (ascii "name" == ascii "filename") = false := by decide
  have hfn : (ascii "filename" == ascii "name") = false := by decide
  cases f <;> simp only [Options.lookup, Option.toList_some, Option.toList_none, List.map_cons, List.map_nil,
    List.find?_cons, beq_self_eq_true, hnf, List.find?_nil, Option.map_some, Option.map_none] <;> rfl

end LeanMultipart
