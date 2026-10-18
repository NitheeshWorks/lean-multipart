import LeanMultipart.RepoImpl.Unquote

/-!
# The fast field decoder is the specification

`unquotePlusLatin1` (the machine pushing characters onto a `String`) and
`unquotePlusLatin1Fast` (the same machine writing UTF-8 bytes, taking each
run without `%` at once) are equal, so `@[csimp]` lets compiled code run the
fast one wherever the specification is called.

The argument has two steps. The machine is generic in its `Sink`, and
`String.toByteArray` turns pushing a character onto a string into pushing
its UTF-8 bytes (`toByteArray_push`), so running on bytes is running on the
string and encoding (`foldl_toBytes`). And a run without `%`, folded byte by
byte, appends the bytes' `encByte`s (`foldl_lit`), which is what the copy and
its fix-up write (`fillA_spec`, `fillB_spec`, `litBulk_eq`), so
`bytesFoldRun_eq` applies.
-/

namespace LeanMultipart
namespace Unquote

/-- The byte-sink state for a string-sink state. -/
def toBytes (s : St String) : St ByteArray := { out := s.out.toByteArray, pct := s.pct, u8 := s.u8 }

theorem ascii_val (c : UInt8) (h : c < 0x80) : (Char.ofNat c.toNat).val.toNat = c.toNat := by
  have hc : c.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h
  have hv : c.toNat.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux]

@[simp] theorem toBytes_pct (s : St String) : (toBytes s).pct = s.pct := rfl
@[simp] theorem toBytes_u8 (s : St String) : (toBytes s).u8 = s.u8 := rfl
theorem toBytes_with_pct (s : St String) (p : Pct) : toBytes { s with pct := p } = { toBytes s with pct := p } := rfl
theorem toBytes_with_u8 (s : St String) (u : U8) : toBytes { s with u8 := u } = { toBytes s with u8 := u } := rfl

theorem pushUtf8_toByteArray (s : String) (c : Char) :
    pushUtf8 s.toByteArray c = (s.push c).toByteArray := by
  rw [String.toByteArray_push, List.utf8Encode_singleton]
  unfold pushUtf8
  split
  · rename_i h
    simp only [String.utf8EncodeChar, h, ↓reduceIte, ByteArray.append_toByteArray_singleton]
  · rfl

theorem emit_toBytes (s : St String) (c : Char) : toBytes (emit s c) = emit (toBytes s) c := by
  show ({ out := (s.out.push c).toByteArray, pct := s.pct, u8 := s.u8 } : St ByteArray) =
    { out := pushUtf8 s.out.toByteArray c, pct := s.pct, u8 := s.u8 }
  rw [pushUtf8_toByteArray]

theorem startByte_toBytes (s : St String) (v : UInt8) : toBytes (startByte s v) = startByte (toBytes s) v := by
  unfold startByte
  repeat' split
  all_goals first | exact emit_toBytes s _ | rfl

theorem lit_toBytes (s : St String) (c : Char) : toBytes (lit s c) = lit (toBytes s) c := by
  unfold lit
  rw [toBytes_u8]
  cases s.u8 with
  | idle => exact emit_toBytes s c
  | seq _ _ _ _ => dsimp only; rw [emit_toBytes, emit_toBytes, toBytes_with_u8]

theorem litByte_toBytes (s : St String) (b : UInt8) : toBytes (litByte s b) = litByte (toBytes s) b := by
  unfold litByte; exact lit_toBytes s _

theorem plain_toBytes (s : St String) (b : UInt8) : toBytes (plain s b) = plain (toBytes s) b := by
  unfold plain; split
  · rfl
  · exact litByte_toBytes s b

theorem escByte_toBytes (s : St String) (v : UInt8) : toBytes (escByte s v) = escByte (toBytes s) v := by
  unfold escByte
  rw [toBytes_u8]
  cases s.u8 with
  | idle => exact startByte_toBytes s v
  | seq need lo hi cp =>
    simp only
    split
    · split
      · rw [emit_toBytes, toBytes_with_u8]
      · rfl
    · rw [startByte_toBytes, emit_toBytes, toBytes_with_u8]

theorem step_toBytes (s : St String) (b : UInt8) : toBytes (step s b) = step (toBytes s) b := by
  unfold step
  rw [toBytes_pct]
  cases s.pct with
  | none => exact plain_toBytes s b
  | pct =>
    simp only
    cases hexVal? b with
    | some x => rfl
    | none => rw [plain_toBytes, lit_toBytes, toBytes_with_pct]
  | hex a x =>
    simp only
    cases hexVal? b with
    | some y => rw [escByte_toBytes, toBytes_with_pct]
    | none => rw [plain_toBytes, litByte_toBytes, lit_toBytes, toBytes_with_pct]

theorem finish_u8 (t : St String) :
    (match t.u8 with | .idle => t.out | .seq .. => (emit t replacement).out).toByteArray =
      (match (toBytes t).u8 with | .idle => (toBytes t).out | .seq .. => (emit (toBytes t) replacement).out) := by
  rw [toBytes_u8]
  cases t.u8 with
  | idle => rfl
  | seq _ _ _ _ => exact congrArg St.out (emit_toBytes t replacement)

theorem finish_toBytes (s : St String) : (finish s).toByteArray = finish (toBytes s) := by
  unfold finish
  rw [toBytes_pct]
  cases s.pct with
  | none => exact finish_u8 s
  | pct => simp only; rw [← toBytes_with_pct, ← lit_toBytes]; exact finish_u8 _
  | hex a x => simp only; rw [← toBytes_with_pct, ← lit_toBytes, ← litByte_toBytes]; exact finish_u8 _

theorem foldl_toBytes : ∀ (l : Bytes) (s : St String), toBytes (l.foldl step s) = l.foldl step (toBytes s) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons c l ih => intro s; rw [List.foldl_cons, List.foldl_cons, ih, step_toBytes]

/-! ## Plain ASCII -/

theorem step_plain (s : St ByteArray) (c : UInt8) (hp : s.pct = .none) (hu : s.u8 = .idle)
    (hc : special c = false) : step s c = { s with out := s.out.push c } := by
  have hlt : c < 0x80 := by
    simp only [special, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    exact UInt8.not_le.mp hc.1.1
  have hpct : (c == Byte.PERCENT) = false := by simp [special] at hc; simpa using hc.1.2
  have hplus : (c == Byte.PLUS) = false := by simp [special] at hc; simpa using hc.2
  obtain ⟨out, p, u⟩ := s
  simp only at hp hu; subst hp; subst hu
  simp only [step, plain, hpct, litByte, hplus, lit, emit, Sink.push, pushUtf8, Bool.false_eq_true, ↓reduceIte]
  have hv := ascii_val c hlt
  have h127 : c.toNat ≤ 127 := by have := UInt8.lt_iff_toNat_lt.mp hlt; simp at this; omega
  simp only [hv, h127, ↓reduceIte]
  simp [UInt8.ofNat_toNat]

theorem foldl_plain : ∀ (l : Bytes) (s : St ByteArray), s.pct = .none → s.u8 = .idle →
    (∀ x ∈ l, special x = false) → l.foldl step s = { s with out := s.out ++ ⟨l.toArray⟩ } := by
  intro l
  induction l with
  | nil => intro s _ _ _; simp
  | cons c l ih =>
    intro s hp hu hl
    rw [List.foldl_cons, step_plain s c hp hu (hl c (by simp)),
      ih { s with out := s.out.push c } hp hu (fun x hx => hl x (by simp [hx]))]
    congr 1
    apply ByteArray.ext_toList; simp [ByteArray.data_append]

/-! ## Runs without `%` -/

theorem char_val (c : UInt8) : (Char.ofNat c.toNat).val.toNat = c.toNat := by
  have hc : c.toNat < 256 := c.toNat_lt
  have hv : c.toNat.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux]

theorem utf8_high (c : UInt8) (h : ¬ c < 0x80) :
    String.utf8EncodeChar (Char.ofNat c.toNat) = if c < 0xC0 then [0xC2, c] else [0xC3, c - 0x40] := by
  have hc : c.toNat < 256 := c.toNat_lt
  have h8 : 128 ≤ c.toNat := by simp [UInt8.lt_iff_toNat_lt] at h; omega
  unfold String.utf8EncodeChar
  simp only [char_val]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  split
  · rename_i hl
    have hl' : c.toNat < 192 := by simpa [UInt8.lt_iff_toNat_lt] using hl
    congr 1
    · apply UInt8.toNat.inj; simp; omega
    · congr 1; apply UInt8.toNat.inj; simp; omega
  · rename_i hl
    have hl' : 192 ≤ c.toNat := by simp [UInt8.lt_iff_toNat_lt] at hl; omega
    congr 1
    · apply UInt8.toNat.inj; simp; omega
    · congr 1; apply UInt8.toNat.inj
      have : (c - 0x40).toNat = c.toNat - 64 := UInt8.toNat_sub_of_le _ _ (by simp [UInt8.le_iff_toNat_le]; omega)
      simp [this]; omega

theorem step_lit (s : St ByteArray) (c : UInt8) (hp : s.pct = .none) (hu : s.u8 = .idle)
    (hc : c ≠ Byte.PERCENT) : step s c = { s with out := s.out ++ ⟨(encByte c).toArray⟩ } := by
  obtain ⟨out, p, u⟩ := s
  simp only at hp hu; subst hp; subst hu
  have hpct : (c == Byte.PERCENT) = false := by simpa using hc
  simp only [step, plain, hpct, litByte, lit, emit, Sink.push, pushUtf8, Bool.false_eq_true, ↓reduceIte, encByte]
  congr 1
  by_cases hlt : c < 0x80
  · simp only [hlt, ↓reduceIte]
    by_cases hplus : c = Byte.PLUS
    · subst hplus; apply ByteArray.ext; simp [Byte.PLUS]
    · have hv := char_val c
      have h127 : c.toNat ≤ 127 := by have := UInt8.lt_iff_toNat_lt.mp hlt; simp at this; omega
      simp only [beq_iff_eq, hplus, ↓reduceIte, hv, h127]
      apply ByteArray.ext; simp [UInt8.ofNat_toNat]
  · have hv := char_val c
    have h127 : ¬ c.toNat ≤ 127 := by simp [UInt8.lt_iff_toNat_lt] at hlt; omega
    have hplus : (c == Byte.PLUS) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; subst h; exact hlt (by decide)
    simp only [hlt, hplus, ↓reduceIte, hv, h127, Bool.false_eq_true, utf8_high c hlt]
    split <;> rfl

theorem foldl_lit : ∀ (l : Bytes) (s : St ByteArray), s.pct = .none → s.u8 = .idle →
    (∀ x ∈ l, x ≠ Byte.PERCENT) → l.foldl step s = { s with out := s.out ++ ⟨(encList l).toArray⟩ } := by
  intro l
  induction l with
  | nil => intro s _ _ _; simp [encList]
  | cons c l ih =>
    intro s hp hu hl
    rw [List.foldl_cons, step_lit s c hp hu (hl c (by simp)),
      ih { s with out := s.out ++ ⟨(encByte c).toArray⟩ } hp hu (fun x hx => hl x (by simp [hx]))]
    congr 1
    apply ByteArray.ext_toList; simp [ByteArray.data_append, encList]

theorem take_put {α : Type} (L : List α) (j : Nat) (x : α) (hj : j ≤ L.length) :
    (L.take j ++ x :: L.drop (j + 1)).take (j + 1) = L.take j ++ [x] := by
  rw [List.take_append, List.take_of_length_le (by simp; omega), List.length_take, Nat.min_eq_left hj,
    Nat.add_sub_cancel_left]
  rfl

theorem drop_put {α : Type} (L : List α) (j : Nat) (x : α) (hj : j ≤ L.length) (e : Nat) :
    (L.take j ++ x :: L.drop (j + 1)).drop (j + 1 + e) = L.drop (j + 1 + e) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.length_take, Nat.min_eq_left hj,
    List.nil_append, show j + 1 + e - j = e + 1 by omega, List.drop_succ_cons, List.drop_drop]

theorem uset_toList (out : ByteArray) (j : USize) (x : UInt8) (h : j.toNat < out.size) :
    (out.uset j x h).data.toList = out.data.toList.take j.toNat ++ x :: out.data.toList.drop (j.toNat + 1) := by
  have h' : j.toNat < out.data.toList.length := by simpa using h
  show (out.data.uset j x h).toList = _
  rw [Array.uset_eq_set, Array.toList_set, List.set_eq_take_append_cons_drop, ite_eq_left h']

theorem set_toList (out : ByteArray) (j : Nat) (x : UInt8) (h : j < out.size) :
    (out.set j x h).data.toList = out.data.toList.take j ++ x :: out.data.toList.drop (j + 1) := by
  have h' : j < out.data.toList.length := by simpa using h
  show (out.data.set j x h).toList = _
  rw [Array.toList_set, List.set_eq_take_append_cons_drop, ite_eq_left h']

theorem fillB_spec (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i j : USize) (out : ByteArray) (hw : out.size < USize.size)
      (hj : j.toNat + (encList (lits b i.toNat stop.toNat)).length ≤ out.size), stop.toNat - i.toNat = n →
      (fillB b stop hs i j out hw hj).data.toList =
        out.data.toList.take j.toNat ++ encList (lits b i.toNat stop.toNat) ++
          out.data.toList.drop (j.toNat + (encList (lits b i.toNat stop.toNat)).length) := by
  intro n
  induction n with
  | zero =>
    intro i j out hw hj hn
    rw [fillB.eq_1]
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [h1, ↓reduceDIte, lits_nil b _ _ (show ¬ i.toNat < stop.toNat by omega), encList,
      List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero, List.take_append_drop]
  | succ n ih =>
    intro i j out hw hj hn
    have hi : i.toNat < stop.toNat := by omega
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; exact hi
    have hi1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    have hl := lits_cons b i.toNat stop.toNat hi hs
    rw [fillB.eq_1]
    simp only [h1, ↓reduceDIte]
    have hget : b.uget i (by omega) = b[i.toNat] := rfl
    have hL : j.toNat ≤ out.data.toList.length := by
      have : 0 < (encList (lits b i.toNat stop.toNat)).length := by
        rw [hl, encList_cons, encByte_length]; split <;> omega
      simp; omega
    split
    · rename_i hlt
      rw [ih (i + 1) (j + 1) _ _ _ (by omega)]
      simp only [uset_toList]
      generalize hcx : b.uget i _ = c at *
      subst hget
      have hjo : j.toNat < out.size := by
        rw [hl, encList_cons, encByte_length, ite_eq_left hlt] at hj; omega
      have hj1 := usize_succ_lt j out.size hjo hw
      rw [hj1, hi1, take_put _ _ _ hL, drop_put _ _ _ hL, hl, encList_cons]
      simp only [encList, List.flatMap_cons, encByte, hlt, ↓reduceIte, List.append_assoc,
        List.cons_append, List.length_cons, List.length_nil]
      rw [show j.toNat + (0 + 1 + (List.flatMap encByte (lits b (i.toNat + 1) stop.toNat)).length) =
        j.toNat + 1 + (List.flatMap encByte (lits b (i.toNat + 1) stop.toNat)).length by omega]
    · rename_i hlt
      rw [hget] at hlt
      have hjo : j.toNat + 1 < out.size := by
        rw [hl, encList_cons, encByte_length, ite_eq_right hlt] at hj; omega
      have hj1 := usize_succ_lt j out.size (by omega) hw
      have hj2 : (j + 2).toNat = j.toNat + 2 := usize_add_toNat j 2 (by omega)
      have key : ∀ (y1 y2 : UInt8) (p1 : j.toNat < out.size) (p2 : (j + 1).toNat < (out.uset j y1 p1).size)
          (q1 : ((out.uset j y1 p1).uset (j + 1) y2 p2).size < USize.size)
          (q2 : (j + 2).toNat + (encList (lits b (i + 1).toNat stop.toNat)).length ≤
            ((out.uset j y1 p1).uset (j + 1) y2 p2).size), encByte b[i.toNat] = [y1, y2] →
          (fillB b stop hs (i + 1) (j + 2) ((out.uset j y1 p1).uset (j + 1) y2 p2) q1 q2).data.toList =
            out.data.toList.take j.toNat ++ encList (lits b i.toNat stop.toNat) ++
              out.data.toList.drop (j.toNat + (encList (lits b i.toNat stop.toNat)).length) := by
        intro y1 y2 p1 p2 q1 q2 hy
        rw [ih (i + 1) (j + 2) _ q1 q2 (by omega)]
        have hL1 : (j + 1).toNat ≤ (out.uset j y1 p1).data.toList.length := by
          rw [hj1]; simp [size_uset']; omega
        rw [uset_toList, hj2, ← show (j + 1).toNat + 1 = j.toNat + 2 by omega, take_put _ _ _ hL1,
          drop_put _ _ _ hL1, hj1, uset_toList, take_put _ _ _ hL,
          show j.toNat + 1 + 1 + (encList (lits b (i + 1).toNat stop.toNat)).length =
            j.toNat + 1 + (1 + (encList (lits b (i + 1).toNat stop.toNat)).length) by omega,
          drop_put _ _ _ hL, hi1, hl, encList_cons, hy]
        simp only [encList, List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.length_cons, List.length_nil]
        rw [show j.toNat + 1 + (1 + (List.flatMap encByte (lits b (i.toNat + 1) stop.toNat)).length) =
          j.toNat + (0 + 1 + 1 + (List.flatMap encByte (lits b (i.toNat + 1) stop.toNat)).length) by omega, hy]
        rfl
      split
      · rename_i h2
        rw [hget] at h2
        exact key _ _ _ _ _ _ (by simp [encByte, hlt, h2, hget])
      · rename_i h2
        rw [hget] at h2
        exact key _ _ _ _ _ _ (by simp [encByte, hlt, h2, hget])

theorem lits_split (b : ByteArray) (i k stop : Nat) (h1 : i ≤ k) (h2 : k ≤ stop) :
    lits b i stop = lits b i k ++ lits b k stop := by
  unfold lits
  rw [show stop - i = (k - i) + (stop - k) by omega, List.take_add, List.drop_drop,
    show i + (k - i) = k by omega]

theorem encList_id (l : Bytes) (h : ∀ x ∈ l, litStop x = false) : encList l = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [encList, List.flatMap_cons] at ih ⊢
    rw [encByte_plain c (h c (by simp)), ih (fun x hx => h x (by simp [hx]))]; rfl

theorem encList_append (l1 l2 : Bytes) : encList (l1 ++ l2) = encList l1 ++ encList l2 := by
  simp [encList]

theorem lits_length (b : ByteArray) (i stop : Nat) (h : stop ≤ b.size) : (lits b i stop).length = stop - i := by
  simp [lits]; omega

theorem fillA_spec (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i j : USize) (out : ByteArray) (hw : out.size + (stop.toNat - i.toNat) < USize.size)
      (hj : j.toNat + (stop.toNat - i.toNat) ≤ out.size) (A : Bytes), stop.toNat - i.toNat = n →
      A.length = j.toNat → out.data.toList = A ++ lits b i.toNat stop.toNat →
      (fillA b stop hs i j out hw hj).data.toList = A ++ encList (lits b i.toNat stop.toNat) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i j out hw hj A hn hA hout
    have hkN := scanUntilU8_eq b litStop stop hs _ i rfl
    have hki := scanUntil_ge b litStop stop.toNat _ i.toNat rfl
    have hkle := scanUntil_le b litStop stop.toNat _ i.toNat rfl
    have hne := scanUntil_ne b litStop stop.toNat _ i.toNat rfl
    rw [fillA.eq_1]
    dsimp only
    obtain ⟨k, hk⟩ : ∃ k, scanUntilU8 b litStop stop hs i = k := ⟨_, rfl⟩
    simp only [hk] at hkN ⊢
    rw [← hkN] at hki hkle hne
    have hid : ∀ k', k' ≤ k.toNat → encList (lits b i.toNat k') = lits b i.toNat k' := fun k' hk' =>
      encList_id _ (by
        intro x hx; apply hne x; unfold lits at hx
        have e : List.take (k' - i.toNat) (List.drop i.toNat b.data.toList) =
            List.take (k' - i.toNat) (List.take (k.toNat - i.toNat) (List.drop i.toNat b.data.toList)) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
        rw [e] at hx; exact List.mem_of_mem_take hx)
    split
    · rename_i h
      have hkS : k.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp h
      have hk2 : k.toNat ≤ stop.toNat := by omega
      have hsplit := lits_split b i.toNat k.toNat stop.toNat hki hk2
      have hlen_ik : (lits b i.toNat k.toNat).length = k.toNat - i.toNat := lits_length b _ _ (by omega)
      have hik : (k - i).toNat = k.toNat - i.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hki)
      have hj' : (j + (k - i)).toNat = j.toNat + (k.toNat - i.toNat) := by
        have hs2 : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add, hik]; exact Nat.mod_eq_of_lt (by omega)
      have hAl : (A ++ lits b i.toNat k.toNat).length = (j + (k - i)).toNat := by simp [hA, hlen_ik, hj']
      have hout2 : out.data.toList = (A ++ lits b i.toNat k.toNat) ++ lits b k.toNat stop.toNat := by
        rw [hout, hsplit]; simp
      have hl := lits_cons b k.toNat stop.toNat hkS hs
      have hget : b.uget k (by omega) = b[k.toNat] := rfl
      have hk1 : (k + 1).toNat = k.toNat + 1 := usize_succ_lt k stop.toNat hkS stop.toNat_lt_two_pow_numBits
      split
      · rename_i hplus
        rw [hget] at hplus
        have hc : b[k.toNat] = Byte.PLUS := by simpa using hplus
        have he : encByte b[k.toNat] = [0x20] := by simp [encByte, hc, Byte.PLUS]
        have hjo : (j + (k - i)).toNat < out.size := by omega
        have hj1 : (j + (k - i) + 1).toNat = (j + (k - i)).toNat + 1 := usize_succ_lt _ out.size hjo (by omega)
        have hout' : (out.uset (j + (k - i)) 0x20 hjo).data.toList =
            (A ++ lits b i.toNat k.toNat ++ [0x20]) ++ lits b (k + 1).toNat stop.toNat := by
          rw [uset_toList, hout2, hl, hk1, ← hAl]
          generalize A ++ lits b i.toNat k.toNat = P
          rw [List.take_left, List.drop_append, List.drop_eq_nil_of_le (by omega),
            List.nil_append, show P.length + 1 - P.length = 1 by omega]
          simp
        have a1 : (A ++ lits b i.toNat k.toNat ++ [0x20]).length = (j + (k - i) + 1).toNat := by
          rw [hj1, ← hAl]; simp; omega
        rw [ih (stop.toNat - (k + 1).toNat) (by omega) (k + 1) _ _ _ _ (A ++ lits b i.toNat k.toNat ++ [0x20])
          rfl a1 hout']
        rw [hsplit, encList_append, hid k.toNat (Nat.le_refl _), hl, hk1]
        simp only [encList, List.flatMap_cons, he]
        simp
      · rename_i hplus
        have hx := countHigh_spec b stop hs (stop.toNat - k.toNat) k 0 rfl (by simp; omega)
        have hlk : (lits b k.toNat stop.toNat).length = stop.toNat - k.toNat := lits_length b _ _ hs
        simp only [USize.toNat_zero, Nat.zero_add, hlk] at hx
        rw [fillB_spec b stop hs (stop.toNat - k.toNat) k (j + (k - i)) _ _ _ rfl]
        rw [copySlice_end, ByteArray.data_append, Array.toList_append, extract_toList, hout2]
        have hdrop : ((A ++ lits b i.toNat k.toNat) ++ lits b k.toNat stop.toNat ++
              (b.data.toList.drop k.toNat).take (countHigh b stop hs k 0).toNat).length ≤
            (j + (k - i)).toNat + (encList (lits b k.toNat stop.toNat)).length := by
          have : ((b.data.toList.drop k.toNat).take (countHigh b stop hs k 0).toNat).length ≤
            (countHigh b stop hs k 0).toNat := List.length_take_le _ _
          simp only [List.length_append, hAl, hlk] at this ⊢; omega
        rw [List.drop_eq_nil_of_le hdrop, List.append_nil, List.append_assoc (A ++ lits b i.toNat k.toNat), ← hAl,
          List.take_left, hsplit, encList_append, hid k.toNat (Nat.le_refl _)]
        simp
    · rename_i h
      have hkS : ¬ k.toNat < stop.toNat := fun h' => h (USize.lt_iff_toNat_lt.mpr h')
      have hall : lits b i.toNat stop.toNat = lits b i.toNat k.toNat := by
        unfold lits; congr 1; rcases hkle with h' | h'
        · omega
        · omega
      rw [hout, hall, hid k.toNat (Nat.le_refl _)]

theorem litSpan_le (s : St ByteArray) (b : ByteArray) (i stop : Nat) : litSpan s b i stop ≤ stop - i := by
  unfold litSpan; split
  · rcases scanFor_le b Byte.PERCENT stop _ i rfl with h | h <;> omega
  · exact Nat.zero_le _

theorem litBulk_eq (s : St ByteArray) (b : ByteArray) (i stop : Nat) :
    litBulk s b i (litSpan s b i stop) = ((b.data.toList.drop i).take (litSpan s b i stop)).foldl step s := by
  unfold litBulk
  split
  · rename_i h; rw [h]; rfl
  · rename_i h0
    split
    · rename_i hg
      have hm : ∃ hp : s.pct = .none, s.u8 = .idle ∧ litSpan s b i stop = scanFor b Byte.PERCENT stop i - i := by
        unfold litSpan at h0 ⊢
        split at h0
        · rename_i hp hu; exact ⟨hp, hu, rfl⟩
        · exact absurd rfl h0
      obtain ⟨hp, hu, hspan⟩ := hm
      have hne : ∀ x ∈ (b.data.toList.drop i).take (litSpan s b i stop), x ≠ Byte.PERCENT := by
        rw [hspan]; exact scanFor_ne b Byte.PERCENT stop _ i rfl
      rw [foldl_lit _ s hp hu hne]
      dsimp only
      congr 1
      apply ByteArray.ext_toList
      generalize litSpan s b i stop = n at *
      have hlits : lits b i (i + n) = (b.data.toList.drop i).take n := by simp [lits]
      obtain ⟨hib, hb, hw⟩ := hg
      have e1 : (i + n).toUSize.toNat = i + n := toNat_toUSize (by omega)
      have e2 : i.toUSize.toNat = i := toNat_toUSize (by omega)
      have e3 : s.out.size.toUSize.toNat = s.out.size := toNat_toUSize (by omega)
      have hout1 : (b.copySlice i s.out s.out.size n false).data.toList =
          s.out.data.toList ++ lits b i.toUSize.toNat (i + n).toUSize.toNat := by
        rw [copySlice_end, ByteArray.data_append, Array.toList_append, extract_toList, e1, e2, hlits]
      rw [fillA_spec b (i + n).toUSize _ n i.toUSize s.out.size.toUSize _ _ _ s.out.data.toList
        (by rw [e1, e2]; omega) (by rw [e3]; simp) hout1, e1, e2, hlits]
      simp [ByteArray.data_append]
    · rfl

end Unquote

open Unquote in
/-- The decoder as compiled: UTF-8 bytes, with each run without `%` taken at once. -/
def unquotePlusLatin1Bytes (raw : ByteArray) : ByteArray :=
  finish (bytesFoldRun step litSpan litBulk (fun _ => false) raw raw.size 0
    ({ out := ByteArray.emptyWithCapacity raw.size } : St ByteArray))

open Unquote in
theorem unquotePlusLatin1Bytes_eq (raw : ByteArray) :
    unquotePlusLatin1Bytes raw = (unquotePlusLatin1 raw).toByteArray := by
  unfold unquotePlusLatin1Bytes unquotePlusLatin1
  rw [bytesFoldRun_eq step litSpan litBulk (fun _ => false) (fun _ _ h => by cases h) litSpan_le
    litBulk_eq raw raw.size _ 0 _ rfl, bytesFold_full, finish_toBytes, foldl_toBytes]
  rfl

open Unquote in
/-- A field with no `%`, `+` or byte `≥ 0x80` decodes to itself. -/
theorem unquotePlusLatin1_plain (raw : ByteArray) (h : scanUntil raw special raw.size 0 = raw.size) :
    (unquotePlusLatin1 raw).toByteArray = raw := by
  have hne := scanUntil_ne raw special raw.size _ 0 rfl
  rw [h, Nat.sub_zero, List.drop_zero, List.take_of_length_le (by simp [Array.length_toList])] at hne
  unfold unquotePlusLatin1
  rw [finish_toBytes, foldl_toBytes, foldl_plain _ _ rfl rfl hne]
  apply ByteArray.ext_toList
  simp [toBytes, finish]

namespace Unquote

theorem specialFlag_zero (c : UInt8) (h : specialFlag c = 0) : special c = false := by
  have tb : ∀ x : Bool, x.toUInt8 = 0 → x = false := by decide
  simp only [specialFlag, UInt8.or_eq_zero_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hc : c.toNat < 128 := by
    have := congrArg UInt8.toNat h1
    rw [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
    simp at this; omega
  have hlt : ¬ 0x80 ≤ c := by simp [UInt8.le_iff_toNat_le]; omega
  simp [special, hlt, tb _ h2, tb _ h3]

theorem specialAny_zero (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i : USize) (acc : UInt8), stop.toNat - i.toNat = n → specialAny b stop hs i acc = 0 →
      acc = 0 ∧ ∀ x ∈ lits b i.toNat stop.toNat, special x = false := by
  intro n
  induction n with
  | zero =>
    intro i acc hn h
    rw [specialAny.eq_1] at h
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [h1, ↓reduceDIte] at h
    refine ⟨h, ?_⟩
    rw [lits_nil b _ _ (by omega)]; simp
  | succ n ih =>
    intro i acc hn h
    have hi : i.toNat < stop.toNat := by omega
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; exact hi
    have hi1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    rw [specialAny.eq_1] at h
    simp only [h1, ↓reduceDIte] at h
    obtain ⟨ha, hrest⟩ := ih (i + 1) _ (by omega) h
    simp only [UInt8.or_eq_zero_iff] at ha
    refine ⟨ha.1, ?_⟩
    rw [lits_cons b i.toNat stop.toNat hi hs]
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact specialFlag_zero _ ha.2
    · rw [hi1] at hrest; exact hrest x hx

theorem unquotePlusLatin1_plain_all (raw : ByteArray) (h : ∀ x ∈ raw.data.toList, special x = false) :
    (unquotePlusLatin1 raw).toByteArray = raw := by
  unfold unquotePlusLatin1
  rw [finish_toBytes, foldl_toBytes, foldl_plain _ _ rfl rfl h]
  apply ByteArray.ext_toList
  simp [toBytes, finish]

theorem specialAny_plain (raw : ByteArray) (hw : raw.size < USize.size)
    (h : specialAny raw raw.size.toUSize (by rw [toNat_toUSize hw]; exact Nat.le_refl _) 0 0 = 0) :
    (unquotePlusLatin1 raw).toByteArray = raw := by
  apply unquotePlusLatin1_plain_all
  have := (specialAny_zero raw raw.size.toUSize _ _ 0 0 rfl h).2
  rw [toNat_toUSize hw] at this
  intro x hx; apply this x
  unfold lits; rw [USize.toNat_zero, Nat.sub_zero, List.drop_zero, List.take_of_length_le (by simp)]; exact hx

theorem pctHighFlag_zero (c : UInt8) (h : pctHighFlag c = 0) : c < 0x80 ∧ c ≠ Byte.PERCENT := by
  have tb : ∀ b : Bool, b.toUInt8 = 0 → b = false := by decide
  simp only [pctHighFlag, UInt8.or_eq_zero_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hc : c.toNat < 128 := by
    have := congrArg UInt8.toNat h1
    rw [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
    simp at this; omega
  refine ⟨UInt8.lt_iff_toNat_lt.mpr (by simpa using hc), ?_⟩
  have := tb _ h2; simpa using this

theorem pctHighAny_zero (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i : USize) (acc : UInt8), stop.toNat - i.toNat = n → pctHighAny b stop hs i acc = 0 →
      acc = 0 ∧ ∀ x ∈ lits b i.toNat stop.toNat, x < 0x80 ∧ x ≠ Byte.PERCENT := by
  intro n
  induction n with
  | zero =>
    intro i acc hn h
    rw [pctHighAny.eq_1] at h
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [h1, ↓reduceDIte] at h
    refine ⟨h, ?_⟩
    rw [lits_nil b _ _ (by omega)]; simp
  | succ n ih =>
    intro i acc hn h
    have hi : i.toNat < stop.toNat := by omega
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; exact hi
    have hi1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    rw [pctHighAny.eq_1] at h
    simp only [h1, ↓reduceDIte] at h
    obtain ⟨ha, hrest⟩ := ih (i + 1) _ (by omega) h
    simp only [UInt8.or_eq_zero_iff] at ha
    refine ⟨ha.1, ?_⟩
    rw [lits_cons b i.toNat stop.toNat hi hs]
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact pctHighFlag_zero _ ha.2
    · rw [hi1] at hrest; exact hrest x hx

theorem plusAt_get (b : ByteArray) (i : USize) (h : i.toNat < b.size) (k : Nat) (hk : k < b.size) :
    (plusAt b i h)[k]'(by rw [size_plusAt]; exact hk) = if i.toNat = k then plusByte b[k] else b[k] := by
  show (b.data.uset i (plusByte (b.uget i h)) h)[k]'(by simpa using hk) = _
  simp only [Array.uset, Array.getElem_set]
  split
  · rename_i he; subst he; rfl
  · rfl

/-- What `plusTail` and `plusMap` compute: from `i` on, each byte mapped. -/
def plusFrom (b : ByteArray) (i : Nat) (k : Nat) (hk : k < b.size) : UInt8 :=
  if i ≤ k then plusByte b[k] else b[k]

theorem plusTail_spec (stop : USize) :
    ∀ (n : Nat) (b : ByteArray) (hs : stop.toNat = b.size) (i : USize), stop.toNat - i.toNat = n →
      ∃ hz : (plusTail b stop hs i).size = b.size,
        ∀ k (hk : k < b.size), (plusTail b stop hs i)[k]'(hz ▸ hk) = plusFrom b i.toNat k hk := by
  intro n
  induction n with
  | zero =>
    intro b hs i hn
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    have e : plusTail b stop hs i = b := by rw [plusTail.eq_1]; simp only [h1, ↓reduceDIte]
    refine ⟨by rw [e], fun k hk => ?_⟩
    have hik : ¬ i.toNat ≤ k := by omega
    simp only [plusFrom, hik, ↓reduceIte]
    congr 1
  | succ n ih =>
    intro b hs i hn
    have hi : i.toNat < stop.toNat := by omega
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; exact hi
    have hi1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    have e : plusTail b stop hs i = plusTail (plusAt b i (by omega)) stop (by rw [size_plusAt]; exact hs) (i + 1) := by
      rw [plusTail.eq_1]; simp only [h1, ↓reduceDIte]
    obtain ⟨hz, hg⟩ := ih (plusAt b i (by omega)) (by rw [size_plusAt]; exact hs) (i + 1) (by omega)
    refine ⟨by rw [e, hz, size_plusAt], fun k hk => ?_⟩
    have hg' := hg k (by rw [size_plusAt]; exact hk)
    simp only [plusFrom, hi1, plusAt_get _ _ _ k hk] at hg' ⊢
    simp only [e]; rw [hg']
    repeat' split
    all_goals first | (exfalso; omega) | rfl | (subst_vars; rfl)

theorem plusMap_spec (stop : USize) :
    ∀ (n : Nat) (b : ByteArray) (hs : stop.toNat = b.size) (i : USize) (hi : i.toNat ≤ stop.toNat),
      stop.toNat - i.toNat = n →
      ∃ hz : (plusMap b stop hs i hi).size = b.size,
        ∀ k (hk : k < b.size), (plusMap b stop hs i hi)[k]'(hz ▸ hk) = plusFrom b i.toNat k hk := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro b hs i hi hn
    rw [plusMap.eq_1]
    split
    · rename_i h
      have h4 : i.toNat + 4 ≤ stop.toNat := by
        rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hi)] at h
        simp at h; omega
      have hlt := stop.toNat_lt_two_pow_numBits
      have hU : USize.size = 2 ^ System.Platform.numBits := rfl
      have e1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
      have e2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
      have e3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
      have e4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
      obtain ⟨hz, hg⟩ := ih (stop.toNat - (i + 4).toNat) (by omega) _ _ (i + 4) _ rfl
      refine ⟨by rw [hz]; simp only [size_plusAt], fun k hk => ?_⟩
      rw [hg k (by simp only [size_plusAt]; exact hk)]
      simp only [plusFrom, e4]
      have hk1 : k < (plusAt b i (by omega)).size := by rw [size_plusAt]; exact hk
      have hk2 : k < (plusAt (plusAt b i (by omega)) (i + 1) (by rw [size_plusAt]; omega)).size := by
        simp only [size_plusAt]; exact hk
      have hk3 : k < (plusAt (plusAt (plusAt b i (by omega)) (i + 1) (by rw [size_plusAt]; omega)) (i + 2)
          (by simp only [size_plusAt]; omega)).size := by simp only [size_plusAt]; exact hk
      rw [plusAt_get _ _ _ k hk3, plusAt_get _ _ _ k hk2, plusAt_get _ _ _ k hk1, plusAt_get _ _ _ k hk,
        e1, e2, e3]
      repeat' split
      all_goals first | (exfalso; omega) | rfl | (subst_vars; rfl)
    · exact plusTail_spec stop _ b hs i rfl

theorem plusByte_enc (c : UInt8) (h : c < 0x80) : encByte c = [plusByte c] := by
  simp only [encByte, h, ↓reduceIte, plusByte]

theorem encList_plus (l : List UInt8) (h : ∀ x ∈ l, x < 0x80) : encList l = l.map plusByte := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [encList, List.flatMap_cons, List.map_cons] at this ⊢
    rw [plusByte_enc c (h c (by simp)), this]; rfl

theorem unquotePlusLatin1_lit_all (raw : ByteArray) (h : ∀ x ∈ raw.data.toList, x ≠ Byte.PERCENT) :
    (unquotePlusLatin1 raw).toByteArray = ⟨(encList raw.data.toList).toArray⟩ := by
  unfold unquotePlusLatin1
  rw [finish_toBytes, foldl_toBytes, foldl_lit _ _ rfl rfl h]
  apply ByteArray.ext_toList
  simp [toBytes, finish]

/-- A field with no `%` and no byte `≥ 0x80` decodes to its bytes with each
`+` mapped to a space, in place. -/
theorem pctHighAny_plus (raw : ByteArray) (hw : raw.size < USize.size)
    (h : pctHighAny raw raw.size.toUSize (by rw [toNat_toUSize hw]; exact Nat.le_refl _) 0 0 = 0) :
    (unquotePlusLatin1 raw).toByteArray = plusMap raw raw.size.toUSize (toNat_toUSize hw) 0 (by simp) := by
  have hall := (pctHighAny_zero raw raw.size.toUSize _ _ 0 0 rfl h).2
  rw [toNat_toUSize hw] at hall
  have hl : lits raw (0 : USize).toNat raw.size = raw.data.toList := by
    unfold lits; rw [USize.toNat_zero, Nat.sub_zero, List.drop_zero, List.take_of_length_le (by simp)]
  rw [hl] at hall
  rw [unquotePlusLatin1_lit_all raw (fun x hx => (hall x hx).2), encList_plus _ (fun x hx => (hall x hx).1)]
  obtain ⟨hz, hg⟩ := plusMap_spec _ _ raw (toNat_toUSize hw) 0 (by simp) rfl
  apply ByteArray.ext_toList
  apply List.ext_getElem
  · simp [hz]
  · intro k h1 h2
    have hk : k < raw.size := by simpa using h1
    have := hg k hk
    simp only [plusFrom, USize.toNat_zero, Nat.zero_le, ↓reduceIte] at this
    simp only [List.getElem_map, Array.getElem_toList]
    exact this.symm

end Unquote

/-- `unquotePlusLatin1`, run fast: a plain field is its own bytes, any other
is decoded with runs copied at once; either way the bytes are valid UTF-8
because they are the specification's string's bytes. -/
def unquotePlusLatin1Fast (raw : ByteArray) : String :=
  if hw : raw.size < USize.size then
    if h : Unquote.specialAny raw raw.size.toUSize (by rw [toNat_toUSize hw]; exact Nat.le_refl _) 0 0 = 0 then
      String.ofByteArray raw (by rw [← Unquote.specialAny_plain raw hw h]; exact (unquotePlusLatin1 raw).isValidUTF8)
    else if h2 : Unquote.pctHighAny raw raw.size.toUSize (by rw [toNat_toUSize hw]; exact Nat.le_refl _) 0 0 = 0 then
      String.ofByteArray (Unquote.plusMap raw raw.size.toUSize (toNat_toUSize hw) 0 (by simp))
        (by rw [← Unquote.pctHighAny_plus raw hw h2]; exact (unquotePlusLatin1 raw).isValidUTF8)
    else
      String.ofByteArray (unquotePlusLatin1Bytes raw)
        (by rw [unquotePlusLatin1Bytes_eq]; exact (unquotePlusLatin1 raw).isValidUTF8)
  else
    String.ofByteArray (unquotePlusLatin1Bytes raw)
      (by rw [unquotePlusLatin1Bytes_eq]; exact (unquotePlusLatin1 raw).isValidUTF8)

@[csimp] theorem unquotePlusLatin1_eq_fast : @unquotePlusLatin1 = @unquotePlusLatin1Fast := by
  funext raw
  apply String.toByteArray_inj.mp
  unfold unquotePlusLatin1Fast
  split
  · split
    · rename_i hw h; exact (Unquote.specialAny_plain raw hw h)
    · split
      · rename_i hw _ h2; exact (Unquote.pctHighAny_plus raw hw h2)
      · exact (unquotePlusLatin1Bytes_eq raw).symm
  · exact (unquotePlusLatin1Bytes_eq raw).symm

end LeanMultipart
