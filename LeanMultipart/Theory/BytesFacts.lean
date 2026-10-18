/-!
# `ByteArray` facts for `simp`

The parsers keep their buffers in `ByteArray`; the proofs read them through
`.data.toList`. These make that view compute.
-/

namespace LeanMultipart

attribute [simp] ByteArray.data_push

@[simp] theorem ByteArray.data_empty' : ByteArray.empty.data = #[] := rfl

@[simp] theorem ByteArray.emptyWithCapacity_eq (n : Nat) : ByteArray.emptyWithCapacity n = ByteArray.empty := rfl

@[simp] theorem ByteArray.mk_nil : (ByteArray.mk #[]) = ByteArray.empty := rfl

attribute [simp] ByteArray.append_empty ByteArray.empty_append

@[simp] theorem ByteArray.data_mk (a : Array UInt8) : (ByteArray.mk a).data = a := rfl

@[simp] theorem ByteArray.append_push' (a b : ByteArray) (c : UInt8) : (a ++ b).push c = a ++ b.push c := by
  apply ByteArray.ext; simp [ByteArray.data_append]

attribute [simp] ByteArray.append_assoc

@[simp] theorem ByteArray.append_empty_push (a : ByteArray) (c : UInt8) : a ++ ByteArray.empty.push c = a.push c := by
  apply ByteArray.ext; simp [ByteArray.data_append]

@[simp] theorem ByteArray.isEmpty_empty' : ByteArray.empty.isEmpty = true := rfl

theorem ByteArray.ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem ByteArray.toList_loop_eq (b : ByteArray) : ∀ (n i : Nat) (r : List UInt8), b.size - i = n →
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r hn
    unfold ByteArray.toList.loop
    simp only [show ¬ i < b.size by omega, ↓reduceIte]
    have : b.data.toList.drop i = [] :=
      List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_sub_eq_zero hn)
    rw [this, List.append_nil]
  | succ n ih =>
    intro i r hn
    unfold ByteArray.toList.loop
    have hi : i < b.size := by omega
    simp only [hi, ↓reduceIte]
    rw [ih (i + 1) _ (by omega)]
    have hl : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.drop_eq_getElem_cons hl]
    have hg : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, Array.getElem_toList, hi]
    simp [hg]

/-- `ByteArray.toList` is the list of the underlying array. -/
@[simp] theorem ByteArray.toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  unfold ByteArray.toList
  rw [ByteArray.toList_loop_eq b _ 0 [] rfl]; simp

end LeanMultipart
