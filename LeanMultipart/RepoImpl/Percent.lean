import LeanMultipart.DataTypes.Bytes

/-!
# Percent-encoding

`percentEncodeL` is Python's `urllib.parse.quote(s, safe="")` on bytes and
`quotePlusL` is `quote_plus(s, safe="")` (space becomes `+`); both emit
upper-case hex. `percentDecodeL` is `unquote_to_bytes`: `%XX` with two hex
digits of either case becomes the byte, any other `%` stays literal, so it
is total. `unquotePlusL` first turns `+` into space, as `unquote_plus` does.

Starlette decodes urlencoded form fields with `unquote_plus`; this is the
byte-level core of that.
-/

namespace LeanMultipart

/-- The upper-case hex digit for `n mod 16`. -/
def hexDigit (n : Nat) : UInt8 :=
  let d := n % 16
  if d < 10 then (48 + d).toUInt8 else (55 + d).toUInt8

/-- The value of a hex digit of either case. -/
def hexVal? (c : UInt8) : Option Nat :=
  if Byte.isDigit c then some (c.toNat - 48)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else none

/-- `%XX` for a byte. -/
def pctTriple (c : UInt8) : Bytes := [Byte.PERCENT, hexDigit (c.toNat / 16), hexDigit c.toNat]

/-- Percent-encode every byte that is not unreserved. -/
def percentEncodeL : Bytes → Bytes
  | [] => []
  | c :: cs => (if Byte.isUnreserved c then [c] else pctTriple c) ++ percentEncodeL cs

/-- Like `percentEncodeL`, but space becomes `+` (`quote_plus`). -/
def quotePlusL : Bytes → Bytes
  | [] => []
  | c :: cs =>
    (if Byte.isUnreserved c then [c] else if c == Byte.SPACE then [Byte.PLUS] else pctTriple c)
      ++ quotePlusL cs

/-- Percent-decode (`unquote_to_bytes`). Never fails. -/
def percentDecodeL : Bytes → Bytes
  | [] => []
  | c :: a :: b :: rest =>
    if c == Byte.PERCENT then
      match hexVal? a, hexVal? b with
      | some x, some y => (x * 16 + y).toUInt8 :: percentDecodeL rest
      | _, _ => c :: percentDecodeL (a :: b :: rest)
    else c :: percentDecodeL (a :: b :: rest)
  | c :: rest => c :: percentDecodeL rest

/-- `+` to space. -/
def plusToSpace (c : UInt8) : UInt8 := if c == Byte.PLUS then Byte.SPACE else c

/-- `unquote_plus` on bytes. -/
def unquotePlusL (l : Bytes) : Bytes := percentDecodeL (l.map plusToSpace)

/-! ## ByteArray wrappers -/

def percentEncode (b : ByteArray) : ByteArray := ⟨(percentEncodeL b.data.toList).toArray⟩
def percentDecode (b : ByteArray) : ByteArray := ⟨(percentDecodeL b.data.toList).toArray⟩
def quotePlus (b : ByteArray) : ByteArray := ⟨(quotePlusL b.data.toList).toArray⟩
def unquotePlus (b : ByteArray) : ByteArray := ⟨(unquotePlusL b.data.toList).toArray⟩

end LeanMultipart
