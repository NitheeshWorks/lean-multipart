import LeanMultipart.RepoImpl.Percent
import LeanMultipart.Theory.Codec
import LeanMultipart.Proofs.ByteFacts

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

theorem foldl_map_eq {α β γ : Type} (f : γ → β → γ) (g : α → β) (l : List α) (init : γ) :
    l.foldl (fun acc c => f acc (g c)) init = (l.map g).foldl f init := by
  induction l generalizing init with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-! ## The percent codec, as an instance of the codec theory

The decoder is a byte machine (`decStep`); the encoder is a `flatMap` of a
per-byte encoding. One `Reads` lemma per byte gives the round trip by
`Reads.flatMap`, on any continuation. -/

/-- The decoder as a machine (it has no input limit). -/
def decMachine : Machine (Array UInt8 × DecPending) := { step := decStep, pos := fun s => s.1.size, limit := none }

/-- The `unquote_plus` decoder: `+` is a space, then `unquote_to_bytes`. -/
def decPlusMachine : Machine (Array UInt8 × DecPending) :=
  { step := fun s c => decStep s (plusToSpace c), pos := fun s => s.1.size, limit := none }

/-- Nothing held back, and `acc` decoded so far. -/
def Decoded (acc : Bytes) (s : Array UInt8 × DecPending) : Prop := s.2 = .none ∧ s.1.toList = acc

/-- One byte of `quote`. -/
def encByte (c : UInt8) : Bytes := if Byte.isUnreserved c then [c] else pctTriple c

/-- One byte of `quote_plus`. -/
def encPlusByte (c : UInt8) : Bytes :=
  if Byte.isUnreserved c then [c] else if c == Byte.SPACE then [Byte.PLUS] else pctTriple c

theorem percentEncodeL_flatMap (l : Bytes) : percentEncodeL l = l.flatMap encByte := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [percentEncodeL, encByte, ih]

theorem quotePlusL_flatMap (l : Bytes) : quotePlusL l = l.flatMap encPlusByte := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [quotePlusL, encPlusByte, ih]

theorem hexDigit_mod (n : Nat) : hexDigit n = hexDigit (n % 16) := by simp [hexDigit]

theorem plusToSpace_hexDigit (n : Nat) : plusToSpace (hexDigit n) = hexDigit n := by
  rw [hexDigit_mod]
  have h : ∀ k : Fin 16, plusToSpace (hexDigit k.val) = hexDigit k.val := by decide
  exact h ⟨n % 16, Nat.mod_lt _ (by decide)⟩

theorem foldl_decStep_triple (a : Array UInt8) (c : UInt8) :
    (pctTriple c).foldl decStep (a, .none) = (a.push c, .none) := by
  simp only [pctTriple, List.foldl_cons, List.foldl_nil, decStep, beq_self_eq_true, ite_true,
    hexVal?_hexDigit]
  rw [byte_of_hex]

theorem map_plusToSpace_pctTriple (c : UInt8) : (pctTriple c).map plusToSpace = pctTriple c := by
  simp only [pctTriple, List.map_cons, List.map_nil, plusToSpace_hexDigit]
  rfl

/-- `%XX` decodes to its byte. -/
theorem reads_pctTriple (c : UInt8) (acc : Bytes) :
    Reads decMachine (Decoded acc) (pctTriple c) (Decoded (acc ++ [c])) := by
  intro s ⟨h1, h2⟩
  obtain ⟨a, p⟩ := s
  simp only at h1 h2; subst h1
  show Decoded _ ((pctTriple c).foldl decStep (a, .none))
  rw [foldl_decStep_triple]
  exact ⟨rfl, by simp [h2]⟩

theorem reads_encByte (c : UInt8) (acc : Bytes) :
    Reads decMachine (Decoded acc) (encByte c) (Decoded (acc ++ [c])) := by
  unfold encByte
  split
  · rename_i hu
    intro s ⟨h1, h2⟩
    obtain ⟨a, p⟩ := s
    simp only at h1 h2; subst h1
    simp [Machine.feed, decMachine, decStep, isUnreserved_ne_percent hu, Decoded, h2]
  · exact reads_pctTriple c acc

/-- The `+` decoder is the plain decoder after `+` → space. -/
theorem decPlus_feed (s : Array UInt8 × DecPending) (l : Bytes) :
    decPlusMachine.feed s l = decMachine.feed s (l.map plusToSpace) := by
  simp only [Machine.feed, decPlusMachine, decMachine]
  exact foldl_map_eq decStep plusToSpace l s

theorem reads_encPlusByte (c : UInt8) (acc : Bytes) :
    Reads decPlusMachine (Decoded acc) (encPlusByte c) (Decoded (acc ++ [c])) := by
  intro s hs
  rw [decPlus_feed]
  unfold encPlusByte
  split
  · rename_i hu
    have : c ≠ Byte.PLUS := by rintro rfl; exact absurd hu (by decide)
    have e : [c].map plusToSpace = encByte c := by simp [encByte, hu, plusToSpace, this]
    rw [e]; exact reads_encByte c acc s hs
  · split
    · rename_i _ hsp
      have : c = Byte.SPACE := by simpa using hsp
      subst this
      obtain ⟨a, p⟩ := s
      obtain ⟨h1, h2⟩ := hs
      simp only at h1 h2; subst h1
      simp [Machine.feed, decMachine, decStep, plusToSpace, Decoded, h2]
    · rw [map_plusToSpace_pctTriple]; exact reads_pctTriple c acc s hs

/-- `percentDecodeL` as the decoder machine. -/
theorem percentDecodeL_eq (l : Bytes) : percentDecodeL l = (decFinish (decMachine.feed (#[], .none) l)).toList := by
  have := foldl_decStep l #[] .none trivial
  simp only [pendingBytes, List.nil_append] at this
  exact this.symm

/-- The percent round trip, on any continuation (`_ext`): an instance of
`Reads.flatMap` with `reads_encByte`. -/
theorem percentDecode_percentEncode_ext (l rest : Bytes) :
    percentDecodeL (percentEncodeL l ++ rest) = l ++ percentDecodeL rest := by
  have hr := Reads.flatMap encByte l (fun acc x _ => reads_encByte x acc) [] (#[], .none) ⟨rfl, rfl⟩
  rw [← percentEncodeL_flatMap] at hr
  rw [percentDecodeL_eq, decMachine.feed_append]
  generalize decMachine.feed (#[], .none) (percentEncodeL l) = st at hr
  obtain ⟨a, p⟩ := st
  obtain ⟨h1, h2⟩ := hr
  simp only at h1 h2; subst h1
  have := foldl_decStep rest a .none trivial
  simp only [pendingBytes, List.nil_append] at this
  show (decFinish (rest.foldl decStep (a, .none))).toList = _
  rw [this, h2]; rfl

theorem percentDecode_percentEncode (l : Bytes) : percentDecodeL (percentEncodeL l) = l := by
  simpa using percentDecode_percentEncode_ext l []

/-- The `quote_plus` round trip, on any continuation: an instance of
`Reads.flatMap` with `reads_encPlusByte`. -/
theorem unquotePlus_quotePlus_ext (l rest : Bytes) :
    unquotePlusL (quotePlusL l ++ rest) = l ++ unquotePlusL rest := by
  have hr := Reads.flatMap encPlusByte l (fun acc x _ => reads_encPlusByte x acc) [] (#[], .none) ⟨rfl, rfl⟩
  rw [← quotePlusL_flatMap, decPlus_feed] at hr
  simp only [unquotePlusL, List.map_append]
  rw [percentDecodeL_eq, decMachine.feed_append]
  generalize decMachine.feed (#[], .none) ((quotePlusL l).map plusToSpace) = st at hr
  obtain ⟨a, p⟩ := st
  obtain ⟨h1, h2⟩ := hr
  simp only at h1 h2; subst h1
  have := foldl_decStep (rest.map plusToSpace) a .none trivial
  simp only [pendingBytes, List.nil_append] at this
  show (decFinish ((rest.map plusToSpace).foldl decStep (a, .none))).toList = _
  rw [this, h2]; rfl

theorem unquotePlus_quotePlus (l : Bytes) : unquotePlusL (quotePlusL l) = l := by
  simpa [unquotePlusL] using unquotePlus_quotePlus_ext l []

end LeanMultipart
