import LeanMultipart.DataTypes.Querystring
import LeanMultipart.RepoImpl.Percent

/-!
# The querystring state machine

Upstream's `QuerystringParser`, one byte at a time. `step` is the whole
machine; feeding a chunk is `List.foldl step`, so feeding chunks one after
another is feeding their concatenation (`Qs.feed_append` in
`Proofs/Querystring.lean`). The callback-style parser `QsParser` threads the
same states and derives upstream's callbacks from each transition.

Semantics, as upstream: fields are separated by `&` only (`;` is data,
`tests/test_multipart.py::test_semicolon_is_data_not_a_field_separator`);
empty segments are skipped; a field's name runs to the first `=`, its value
from there to the next `&`; a field with no `=` has an empty value. In
strict mode a second consecutive `&` and a field without `=` that is followed
by `&` are errors.

`maxSize` truncates the input, as upstream's `max_size` does.
-/

namespace LeanMultipart
namespace Qs

/-- Close the current field. -/
def finishField (s : QsState) : QsState :=
  { s with fields := s.fields.push (⟨s.name⟩, ⟨s.value⟩), name := #[], value := #[] }

/-- A byte of a field name (or the `=` / `&` that ends it). `p` is the
byte's offset. -/
def nameByte (cfg : QsConfig) (s : QsState) (c : UInt8) : QsState :=
  if c == Byte.EQ then { s with phase := .fieldData }
  else if c == Byte.AMP then
    if cfg.strict then { s with phase := .failed ⟨.missingEquals, s.nameStart⟩ }
    else { finishField s with phase := .beforeField true }
  else { s with phase := .fieldName, name := s.name.push c }

/-- The transition function. Every byte advances `pos`. -/
def step (cfg : QsConfig) (s : QsState) (c : UInt8) : QsState :=
  let p := s.pos
  let s := { s with pos := p + 1 }
  match s.phase with
  | .failed _ => s
  | .beforeField fs =>
    if c == Byte.AMP then
      if fs then
        if cfg.strict then { s with phase := .failed ⟨.duplicateAmpersand, p⟩ } else s
      else { s with phase := .beforeField true }
    else nameByte cfg { s with nameStart := p, name := #[], value := #[] } c
  | .fieldName => nameByte cfg s c
  | .fieldData =>
    if c == Byte.AMP then { finishField s with phase := .beforeField true }
    else { s with value := s.value.push c }

/-- Feed bytes (no truncation). -/
def feed (cfg : QsConfig) (s : QsState) (l : Bytes) : QsState := l.foldl (step cfg) s

/-- How many more bytes `maxSize` allows. -/
def room (cfg : QsConfig) (s : QsState) (n : Nat) : Nat :=
  match cfg.maxSize with
  | none => n
  | some m => min n (m - s.pos)

/-- Feed bytes, truncated at `maxSize`. -/
def feedT (cfg : QsConfig) (s : QsState) (l : Bytes) : QsState :=
  feed cfg s (l.take (room cfg s l.length))

/-- Feeding the chunks of a list one after another, as a `QsParser` does. -/
def feedChunks (cfg : QsConfig) (s : QsState) : List Bytes → QsState
  | [] => s
  | c :: cs => feedChunks cfg (feedT cfg s c) cs

/-- The number of bytes the whole-buffer parser processes. -/
def processed (cfg : QsConfig) (l : Bytes) : Nat := (feedT cfg {} l).pos

/-- End of input: close a field in progress. -/
def finish (s : QsState) : QsState :=
  match s.phase with
  | .fieldName | .fieldData => { finishField s with phase := .beforeField false }
  | _ => s

/-- The result of a finished state. -/
def result (s : QsState) : Except QsError (List QsField) :=
  match (finish s).phase with
  | .failed e => .error e
  | _ => .ok (finish s).fields.toList

/-- The whole-buffer parser, on a list. -/
def parseL (cfg : QsConfig) (l : Bytes) : Except QsError (List QsField) :=
  result (feedT cfg {} l)

/-- Feed a byte array, truncated at `maxSize`, as an array fold (no
intermediate list). Equal to `feedT` on the list (`Qs.feedA_eq`). -/
def feedA (cfg : QsConfig) (s : QsState) (b : ByteArray) : QsState :=
  (b.data.extract 0 (room cfg s b.size)).foldl (step cfg) s

/-- The whole-buffer parser. Equal to `parseL` on the bytes (`Qs.parse_eq`). -/
def parse (cfg : QsConfig) (b : ByteArray) : Except QsError (List QsField) :=
  result (feedA cfg {} b)

end Qs

/-! ## urlencode / urldecode -/

/-- One `name=value` pair, `quote_plus`-encoded. -/
def encodePairL (p : Bytes × Bytes) : Bytes := quotePlusL p.1 ++ [Byte.EQ] ++ quotePlusL p.2

/-- `urllib.parse.urlencode` on byte pairs: pairs joined by `&`. -/
def urlencodeL : List (Bytes × Bytes) → Bytes
  | [] => []
  | [p] => encodePairL p
  | p :: ps => encodePairL p ++ [Byte.AMP] ++ urlencodeL ps

/-- Decode a body: the non-strict parser, then `unquote_plus` on each name
and value. Total: the non-strict parser has no error case. -/
def urldecodeL (l : Bytes) : List (Bytes × Bytes) :=
  match Qs.parseL {} l with
  | .ok fs => fs.map (fun f => (unquotePlusL f.1.data.toList, unquotePlusL f.2.data.toList))
  | .error _ => []

/-- `urlencode` on byte arrays. -/
def urlencodeB (ps : List (ByteArray × ByteArray)) : ByteArray :=
  ⟨(urlencodeL (ps.map fun p => (p.1.data.toList, p.2.data.toList))).toArray⟩

/-- `urldecode` on byte arrays. -/
def urldecodeB (b : ByteArray) : List (ByteArray × ByteArray) :=
  (urldecodeL b.data.toList).map fun p => (⟨p.1.toArray⟩, ⟨p.2.toArray⟩)

/-- `urlencode` on strings: UTF-8, then `quote_plus`. The result is ASCII. -/
def urlencodeStr (ps : List (String × String)) : String :=
  latin1Decode (urlencodeB (ps.map fun p => (p.1.toUTF8, p.2.toUTF8)))

/-- `urldecode` on strings: each name and value is UTF-8 if valid, else
Latin-1. -/
def urldecodeStr (s : String) : List (String × String) :=
  (urldecodeB s.toUTF8).map fun p => (decodeUtf8OrLatin1 p.1, decodeUtf8OrLatin1 p.2)

end LeanMultipart
