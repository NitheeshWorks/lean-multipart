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
  simp [percentEncode, percentEncodeTR_eq]

theorem percentDecode_toList (b : ByteArray) : (percentDecode b).data.toList = percentDecodeL b.data.toList := by
  simp [percentDecode, percentDecodeTR_eq]

theorem quotePlus_toList (b : ByteArray) : (quotePlus b).data.toList = quotePlusL b.data.toList := by
  simp [quotePlus, quotePlusTR_eq]

theorem unquotePlus_toList (b : ByteArray) : (unquotePlus b).data.toList = unquotePlusL b.data.toList := by
  simp [unquotePlus, unquotePlusL, percentDecodeTR_eq]

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
