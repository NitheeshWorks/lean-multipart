/-!
# Bytes and character classes

The byte constants and the character classes every parser in this library
uses. Each class is a `Bool`-valued function so it is decidable by
construction; the same function is evaluated at runtime and rewritten in
proofs.

Inputs are `ByteArray` at the API and `List UInt8` in the specifications, so
the proofs are list inductions. `ByteArray.data.toList` converts.
-/

namespace LeanMultipart

/-- A byte string in the specifications. -/
abbrev Bytes := List UInt8

namespace Byte

def CR : UInt8 := 13
def LF : UInt8 := 10
def SPACE : UInt8 := 32
def HYPHEN : UInt8 := 45
def COLON : UInt8 := 58
def AMP : UInt8 := 38
def EQ : UInt8 := 61
def PERCENT : UInt8 := 37
def PLUS : UInt8 := 43
def SEMI : UInt8 := 59
def DQUOTE : UInt8 := 34
def BSLASH : UInt8 := 92

/-- `0-9`. -/
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
/-- `A-Z`. -/
def isUpper (c : UInt8) : Bool := 65 ≤ c && c ≤ 90
/-- `a-z`. -/
def isLower (c : UInt8) : Bool := 97 ≤ c && c ≤ 122
/-- ASCII letters. -/
def isAlpha (c : UInt8) : Bool := isUpper c || isLower c

/-- RFC 7230 §3.2.6 `tchar`: the bytes upstream accepts in a part's header
name (`TOKEN_CHARS` in `multipart.py`). -/
def isTokenChar (c : UInt8) : Bool :=
  isAlpha c || isDigit c ||
  c == 33 || c == 35 || c == 36 || c == 37 || c == 38 || c == 39 || c == 42 ||
  c == 43 || c == 45 || c == 46 || c == 94 || c == 95 || c == 96 || c == 124 ||
  c == 126

/-- RFC 2046 §5.1.1 `bchars`: digits, letters and `'()+_,-./:=? ` (space). -/
def isBoundaryChar (c : UInt8) : Bool :=
  isAlpha c || isDigit c ||
  c == 39 || c == 40 || c == 41 || c == 43 || c == 95 || c == 44 || c == 45 ||
  c == 46 || c == 47 || c == 58 || c == 61 || c == 63 || c == 32

/-- The bytes `quote_plus(safe="")` leaves alone: letters, digits and `_.-~`
(Python's `urllib.parse._ALWAYS_SAFE`). -/
def isUnreserved (c : UInt8) : Bool :=
  isAlpha c || isDigit c || c == 95 || c == 46 || c == 45 || c == 126

/-- ASCII lower-casing, as `bytes.lower()` does. -/
def toLowerAscii (c : UInt8) : UInt8 := if isUpper c then c + 32 else c

/-- Python `str.isspace` restricted to Latin-1 code points, which is what
upstream's `str.strip()` sees after `decode("latin-1")`. -/
def isPySpace (c : UInt8) : Bool :=
  (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32) || c == 133 || c == 160

/-- Python `str.lower` restricted to Latin-1 code points: ASCII `A-Z`, and
`À-Þ` except `×`. -/
def pyLower (c : UInt8) : UInt8 :=
  if isUpper c then c + 32
  else if 192 ≤ c && c ≤ 222 && c != 215 then c + 32
  else c

end Byte

/-- Bytes of an ASCII string literal (for the constants below and the tests). -/
def ascii (s : String) : Bytes := s.toList.map (fun c => c.toNat.toUInt8)

/-- ASCII lower-casing of a byte string. -/
def lowerAscii (b : ByteArray) : ByteArray := ⟨b.data.map Byte.toLowerAscii⟩

/-- Latin-1 decoding: every byte is the code point of the same value. Total. -/
def latin1Decode (b : ByteArray) : String :=
  String.ofList (b.data.toList.map (fun c => Char.ofNat c.toNat))

/-- UTF-8 if the bytes are valid UTF-8, else Latin-1. This is Starlette's
`_user_safe_decode` with the default `utf-8` codec. -/
def decodeUtf8OrLatin1 (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => latin1Decode b

end LeanMultipart
