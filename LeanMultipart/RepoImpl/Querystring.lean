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

/-- The whole-buffer parser. -/
def parse (cfg : QsConfig) (b : ByteArray) : Except QsError (List QsField) :=
  parseL cfg b.data.toList

end Qs

/-! ## The callback-style parser -/

/-- Upstream's `QuerystringParser` object: the machine state plus how much
of the current name and value has already been reported. -/
structure QsParser where
  cfg : QsConfig := {}
  st : QsState := {}
  nameSent : Nat := 0
  valueSent : Nat := 0
  deriving Inhabited

namespace QsParser

private def slice (a : Array UInt8) (i : Nat) : ByteArray := ⟨a.extract i a.size⟩

private def emitIf (evs : Array QsEvent) (b : ByteArray) (mk : ByteArray → QsEvent) :
    Array QsEvent :=
  if b.size == 0 then evs else evs.push (mk b)

/-- One byte: the next state and the callbacks the transition fires. -/
def stepEv (p : QsParser) (evs : Array QsEvent) (c : UInt8) : QsParser × Array QsEvent :=
  let s := p.st
  let s' := Qs.step p.cfg s c
  match s.phase, s'.phase with
  | .beforeField _, .fieldName => ({ p with st := s', nameSent := 0, valueSent := 0 }, evs.push .fieldStart)
  | .beforeField _, .fieldData => ({ p with st := s', nameSent := 0, valueSent := 0 }, evs.push .fieldStart)
  | .fieldName, .fieldData =>
    ({ p with st := s', nameSent := s.name.size }, emitIf evs (slice s.name p.nameSent) .fieldName)
  | .fieldName, .beforeField _ =>
    ({ p with st := s', nameSent := 0 },
      (emitIf evs (slice s.name p.nameSent) .fieldName).push .fieldEnd)
  | .fieldData, .beforeField _ =>
    ({ p with st := s', valueSent := 0 },
      (emitIf evs (slice s.value p.valueSent) .fieldData).push .fieldEnd)
  | _, _ => ({ p with st := s' }, evs)

/-- Report what is buffered for the field in progress (end of a chunk). -/
def flush (p : QsParser) (evs : Array QsEvent) : QsParser × Array QsEvent :=
  match p.st.phase with
  | .fieldName =>
    ({ p with nameSent := p.st.name.size }, emitIf evs (slice p.st.name p.nameSent) .fieldName)
  | .fieldData =>
    ({ p with valueSent := p.st.value.size }, emitIf evs (slice p.st.value p.valueSent) .fieldData)
  | _ => (p, evs)

/-- A fresh parser. -/
def new (cfg : QsConfig := {}) : QsParser := { cfg }

/-- Upstream's `write`: feed a chunk, get the callbacks it fires and the
number of bytes processed (fewer than the chunk only under `maxSize`). -/
def write (p : QsParser) (chunk : ByteArray) : QsParser × Array QsEvent × Nat :=
  let n := Qs.room p.cfg p.st chunk.size
  let (p', evs) := (chunk.data.extract 0 n).foldl (fun (acc : QsParser × Array QsEvent) c =>
    stepEv acc.1 acc.2 c) (p, #[])
  let (p'', evs') := flush p' evs
  (p'', evs', n)

/-- Upstream's `finalize`: close a field in progress, then `end`. -/
def finalize (p : QsParser) : QsParser × Array QsEvent :=
  let (p', evs) := flush p #[]
  match p'.st.phase with
  | .fieldName | .fieldData =>
    ({ p' with st := Qs.finish p'.st, nameSent := 0, valueSent := 0 }, (evs.push .fieldEnd).push .end)
  | _ => (p', evs.push .end)

/-- The error, if the machine has failed. -/
def error? (p : QsParser) : Option QsError :=
  match p.st.phase with
  | .failed e => some e
  | _ => none

end QsParser

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

end LeanMultipart
