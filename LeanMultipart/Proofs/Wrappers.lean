import LeanMultipart.Proofs.Querystring
import LeanMultipart.Proofs.MultipartStream

/-!
# Byte-array forms of the list theorems

The specifications are on `List UInt8`; the API is on `ByteArray`. These
lemmas move the round trips across.
-/

namespace LeanMultipart

@[simp] theorem bytes_toList_toArray (l : Bytes) : (ByteArray.mk l.toArray).data.toList = l := by simp

@[simp] theorem bytes_mk_toArray_toList (b : ByteArray) : ByteArray.mk b.data.toList.toArray = b := by
  cases b; simp

theorem percentEncode_toList (b : ByteArray) : (percentEncode b).data.toList = percentEncodeL b.data.toList := by
  simp only [percentEncode, ← Array.foldl_toList, foldl_encStep]; rfl

theorem percentDecode_toList (b : ByteArray) : (percentDecode b).data.toList = percentDecodeL b.data.toList := by
  simp only [percentDecode, ← Array.foldl_toList]
  rw [foldl_decStep _ _ .none trivial]; rfl

theorem quotePlus_toList (b : ByteArray) : (quotePlus b).data.toList = quotePlusL b.data.toList := by
  simp only [quotePlus, ← Array.foldl_toList, foldl_encPlusStep]; rfl

theorem foldl_map_eq {α β γ : Type} (f : γ → β → γ) (g : α → β) (l : List α) (init : γ) :
    l.foldl (fun acc c => f acc (g c)) init = (l.map g).foldl f init := by
  induction l generalizing init with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem unquotePlus_toList (b : ByteArray) : (unquotePlus b).data.toList = unquotePlusL b.data.toList := by
  simp only [unquotePlus, ← Array.foldl_toList, unquotePlusL]
  rw [foldl_map_eq decStep plusToSpace, foldl_decStep _ _ .none trivial]; rfl

theorem byteArray_ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem percentDecode_percentEncodeB (b : ByteArray) : percentDecode (percentEncode b) = b := by
  apply byteArray_ext_toList
  rw [percentDecode_toList, percentEncode_toList, percentDecode_percentEncode]

theorem unquotePlus_quotePlusB (b : ByteArray) : unquotePlus (quotePlus b) = b := by
  apply byteArray_ext_toList
  rw [unquotePlus_toList, quotePlus_toList, unquotePlus_quotePlus]

theorem urldecodeB_urlencodeB (ps : List (ByteArray × ByteArray)) : urldecodeB (urlencodeB ps) = ps := by
  simp only [urldecodeB, urlencodeB, bytes_toList_toArray, Qs.urldecode_urlencode, List.map_map]
  conv => rhs; rw [← List.map_id ps]
  apply List.map_congr_left
  intro p _
  simp

end LeanMultipart
