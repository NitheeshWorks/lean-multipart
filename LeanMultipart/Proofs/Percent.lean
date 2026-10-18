import LeanMultipart.RepoImpl.Percent

/-!
# Percent-encoding: proofs

`percentDecode_percentEncode`: decoding undoes encoding, on any continuation
of the buffer (`_ext`). Likewise for the `+`-for-space variants. The hex
digit lemma is closed by `decide` over `Fin 16`.
-/

namespace LeanMultipart

@[simp] theorem percentDecodeL_nil : percentDecodeL [] = [] := rfl

theorem hexVal?_hexDigit_fin : ∀ n : Fin 16, hexVal? (hexDigit n.val) = some n.val := by decide

theorem hexVal?_hexDigit (n : Nat) : hexVal? (hexDigit n) = some (n % 16) := by
  have h : hexDigit n = hexDigit (n % 16) := by simp [hexDigit]
  rw [h]
  exact hexVal?_hexDigit_fin ⟨n % 16, Nat.mod_lt _ (by decide)⟩

theorem byte_of_hex (c : UInt8) : ((c.toNat / 16 % 16) * 16 + c.toNat % 16).toUInt8 = c := by
  have h := c.toNat_lt
  rw [← UInt8.toNat_inj]
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

/-- Decoding passes a byte other than `%` through unchanged. -/
theorem percentDecodeL_cons_of_ne {c : UInt8} (h : c ≠ Byte.PERCENT) (l : Bytes) :
    percentDecodeL (c :: l) = c :: percentDecodeL l := by
  match l with
  | [] => simp [percentDecodeL]
  | [a] => simp [percentDecodeL]
  | a :: b :: r => simp [percentDecodeL, h]

/-- Decoding turns a well-formed `%XX` back into its byte. -/
theorem percentDecodeL_pctTriple (c : UInt8) (rest : Bytes) :
    percentDecodeL (pctTriple c ++ rest) = c :: percentDecodeL rest := by
  simp only [pctTriple, List.cons_append, List.nil_append, percentDecodeL, beq_self_eq_true,
    ite_true, hexVal?_hexDigit]
  rw [byte_of_hex]

theorem isUnreserved_ne_percent {c : UInt8} (h : Byte.isUnreserved c = true) :
    c ≠ Byte.PERCENT := by
  rintro rfl; exact absurd h (by decide)

/-- The percent-encoding round trip, on any continuation of the buffer. -/
theorem percentDecode_percentEncode_ext (l rest : Bytes) :
    percentDecodeL (percentEncodeL l ++ rest) = l ++ percentDecodeL rest := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [percentEncodeL, List.append_assoc]
    by_cases hu : Byte.isUnreserved c = true
    · simp only [hu, ite_true, List.singleton_append]
      rw [percentDecodeL_cons_of_ne (isUnreserved_ne_percent hu), ih]; rfl
    · simp only [hu, ite_false, Bool.false_eq_true]
      rw [percentDecodeL_pctTriple, ih]; rfl

/-- The percent-encoding round trip. -/
theorem percentDecode_percentEncode (l : Bytes) : percentDecodeL (percentEncodeL l) = l := by
  simpa using percentDecode_percentEncode_ext l []

/-- `quote_plus` output, with `+` turned back into space, is plain
percent-encoding that leaves spaces alone. -/
def quoteSpaceL : Bytes → Bytes
  | [] => []
  | c :: cs =>
    (if Byte.isUnreserved c then [c] else if c == Byte.SPACE then [Byte.SPACE] else pctTriple c)
      ++ quoteSpaceL cs

theorem map_plusToSpace_pctTriple (c : UInt8) : (pctTriple c).map plusToSpace = pctTriple c := by
  have h1 : ∀ n : Fin 16, plusToSpace (hexDigit n.val) = hexDigit n.val := by decide
  have h2 := h1 ⟨c.toNat / 16 % 16, Nat.mod_lt _ (by decide)⟩
  have h3 := h1 ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
  have e1 : hexDigit (c.toNat / 16) = hexDigit (c.toNat / 16 % 16) := by simp [hexDigit]
  have e2 : hexDigit c.toNat = hexDigit (c.toNat % 16) := by simp [hexDigit]
  simp only [pctTriple, List.map_cons, List.map_nil, e1, e2, h2, h3]
  rfl

theorem map_plusToSpace_quotePlusL (l : Bytes) : (quotePlusL l).map plusToSpace = quoteSpaceL l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [quotePlusL, quoteSpaceL, List.map_append, ih]
    congr 1
    by_cases hu : Byte.isUnreserved c = true
    · have : c ≠ Byte.PLUS := by rintro rfl; exact absurd hu (by decide)
      simp [hu, plusToSpace, this]
    · by_cases hs : c = Byte.SPACE
      · subst hs; simp [hu]; decide
      · simp [hu, hs, map_plusToSpace_pctTriple]

theorem percentDecodeL_quoteSpaceL_ext (l rest : Bytes) :
    percentDecodeL (quoteSpaceL l ++ rest) = l ++ percentDecodeL rest := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [quoteSpaceL, List.append_assoc]
    by_cases hu : Byte.isUnreserved c = true
    · simp only [hu, ite_true, List.singleton_append]
      rw [percentDecodeL_cons_of_ne (isUnreserved_ne_percent hu), ih]; rfl
    · by_cases hs : c = Byte.SPACE
      · subst hs
        simp only [hu, ite_false, Bool.false_eq_true, beq_self_eq_true, ite_true, List.singleton_append]
        rw [percentDecodeL_cons_of_ne (by decide), ih]; rfl
      · have : (c == Byte.SPACE) = false := by simpa using hs
        simp only [hu, ite_false, Bool.false_eq_true, this]
        rw [percentDecodeL_pctTriple, ih]; rfl

/-- The `quote_plus` / `unquote_plus` round trip, on any continuation. -/
theorem unquotePlus_quotePlus_ext (l rest : Bytes) :
    unquotePlusL (quotePlusL l ++ rest) = l ++ unquotePlusL rest := by
  simp only [unquotePlusL, List.map_append, map_plusToSpace_quotePlusL]
  exact percentDecodeL_quoteSpaceL_ext l _

theorem unquotePlus_quotePlus (l : Bytes) : unquotePlusL (quotePlusL l) = l := by
  simpa [unquotePlusL] using unquotePlus_quotePlus_ext l []

/-- `quote_plus` output contains neither `&` nor `=`, so it can sit inside a
urlencoded pair. -/
theorem quotePlusL_no_sep (l : Bytes) : ∀ c ∈ quotePlusL l, c ≠ Byte.AMP ∧ c ≠ Byte.EQ := by
  induction l with
  | nil => simp [quotePlusL]
  | cons c cs ih =>
    intro x hx
    simp only [quotePlusL, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hu : Byte.isUnreserved c = true
      · simp only [hu, ite_true, List.mem_singleton] at hx; subst hx
        constructor <;> (rintro rfl; exact absurd hu (by decide))
      · simp only [hu, ite_false, Bool.false_eq_true] at hx
        by_cases hs : (c == Byte.SPACE) = true
        · simp only [hs, ite_true, List.mem_singleton] at hx; subst hx; decide
        · simp only [hs, ite_false, Bool.false_eq_true, pctTriple, List.mem_cons,
            List.not_mem_nil, or_false] at hx
          have hd : ∀ n : Fin 16, hexDigit n.val ≠ Byte.AMP ∧ hexDigit n.val ≠ Byte.EQ := by decide
          have e1 : hexDigit (c.toNat / 16) = hexDigit (c.toNat / 16 % 16) := by simp [hexDigit]
          have e2 : hexDigit c.toNat = hexDigit (c.toNat % 16) := by simp [hexDigit]
          rcases hx with rfl | rfl | rfl
          · decide
          · rw [e1]; exact hd ⟨_, Nat.mod_lt _ (by decide)⟩
          · rw [e2]; exact hd ⟨_, Nat.mod_lt _ (by decide)⟩
    · exact ih x hx

/-! ## The array folds equal the list forms -/

theorem foldl_encStep (l : Bytes) (acc : Array UInt8) :
    (l.foldl encStep acc).toList = acc.toList ++ percentEncodeL l := by
  induction l generalizing acc with
  | nil => simp [percentEncodeL]
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, percentEncodeL, encStep]
    split <;> simp

theorem foldl_encPlusStep (l : Bytes) (acc : Array UInt8) :
    (l.foldl encPlusStep acc).toList = acc.toList ++ quotePlusL l := by
  induction l generalizing acc with
  | nil => simp [quotePlusL]
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, quotePlusL, encPlusStep]
    split
    · simp_all
    · split <;> simp_all

/-- The bytes a pending state stands for. -/
def pendingBytes : DecPending → Bytes
  | .none => []
  | .pct => [Byte.PERCENT]
  | .pctHex a _ => [Byte.PERCENT, a]

/-- A pending `%XX` prefix is consistent: its digit's value is recorded. -/
def PendingOK : DecPending → Prop
  | .pctHex a x => hexVal? a = some x
  | _ => True

theorem hex_ne_percent {a : UInt8} {x : Nat} (h : hexVal? a = some x) : a ≠ Byte.PERCENT := by
  rintro rfl; simp [hexVal?, Byte.PERCENT, Byte.isDigit] at h

theorem percentDecodeL_pct_nonhex (c : UInt8) (l : Bytes) (hc : hexVal? c = none) :
    percentDecodeL (Byte.PERCENT :: c :: l) = Byte.PERCENT :: percentDecodeL (c :: l) := by
  cases l with
  | nil => simp [percentDecodeL]
  | cons b r => simp [percentDecodeL, hc]

theorem percentDecodeL_pct_hex_nonhex (a c : UInt8) (x : Nat) (l : Bytes) (ha : hexVal? a = some x)
    (hc : hexVal? c = none) :
    percentDecodeL (Byte.PERCENT :: a :: c :: l) = Byte.PERCENT :: a :: percentDecodeL (c :: l) := by
  simp [percentDecodeL, hc, ha]
  exact percentDecodeL_cons_of_ne (hex_ne_percent ha) _

theorem foldl_decStep (l : Bytes) : ∀ (acc : Array UInt8) (p : DecPending), PendingOK p →
    (decFinish (l.foldl decStep (acc, p))).toList = acc.toList ++ percentDecodeL (pendingBytes p ++ l) := by
  induction l with
  | nil =>
    intro acc p hp
    cases p with
    | none => simp [decFinish, pendingBytes]
    | pct => simp [decFinish, pendingBytes, percentDecodeL]
    | pctHex a x => simp [decFinish, pendingBytes, percentDecodeL]
  | cons c cs ih =>
    intro acc p hp
    cases p with
    | none =>
      simp only [List.foldl_cons, decStep, pendingBytes, List.nil_append]
      by_cases hc : c = Byte.PERCENT
      · subst hc; simp only [beq_self_eq_true, ite_true]; rw [ih _ .pct trivial]; rfl
      · simp only [show (c == Byte.PERCENT) = false by simpa using hc, Bool.false_eq_true, ite_false]
        rw [ih _ .none trivial, percentDecodeL_cons_of_ne hc]; simp [pendingBytes]
    | pct =>
      simp only [List.foldl_cons, decStep, pendingBytes]
      cases hx : hexVal? c with
      | some x => simp only; rw [ih _ (.pctHex c x) hx]; rfl
      | none =>
        simp only
        by_cases hc : c = Byte.PERCENT
        · subst hc; simp only [beq_self_eq_true, ite_true]; rw [ih _ .pct trivial]
          simp [pendingBytes, percentDecodeL_pct_nonhex _ _ hx]
        · simp only [show (c == Byte.PERCENT) = false by simpa using hc, Bool.false_eq_true, ite_false]
          rw [ih _ .none trivial]
          simp [pendingBytes, percentDecodeL_pct_nonhex _ _ hx, percentDecodeL_cons_of_ne hc]
    | pctHex a x =>
      simp only [List.foldl_cons, decStep, pendingBytes]
      cases hy : hexVal? c with
      | some y =>
        simp only; rw [ih _ .none trivial]
        have hp' : hexVal? a = some x := hp
        simp [pendingBytes, percentDecodeL, hp', hy]
      | none =>
        have hp' : hexVal? a = some x := hp
        simp only
        by_cases hc : c = Byte.PERCENT
        · subst hc; simp only [beq_self_eq_true, ite_true]; rw [ih _ .pct trivial]
          simp [pendingBytes, percentDecodeL_pct_hex_nonhex _ _ _ _ hp' hy]
        · simp only [show (c == Byte.PERCENT) = false by simpa using hc, Bool.false_eq_true, ite_false]
          rw [ih _ .none trivial]
          simp [pendingBytes, percentDecodeL_pct_hex_nonhex _ _ _ _ hp' hy, percentDecodeL_cons_of_ne hc]

end LeanMultipart
