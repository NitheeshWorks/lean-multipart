import LeanMultipart.RepoImpl.Querystring

/-!
# The callback-style querystring parser

Upstream's `QuerystringParser` object, `write` / `finalize`, emitting the
callbacks as `QsEvent`s. It runs the same `Qs.step` as the whole-buffer
parser. To stream in constant memory beyond the current chunk it forgets
what it has already reported: completed fields, and the name or value bytes
flushed at the end of a chunk. `Proofs/Stream.lean` proves that the parser's
state is the whole-buffer state with exactly those buffers cleared
(`QsParser.st_writeAll`), so phase, position and errors agree with
`Qs.parse` for every chunking.

Errors: `write` returns the error instead of events, as upstream raises.
The error's `offset` is absolute in the stream; `chunkOffset` is relative to
the chunk passed to this `write` (upstream's `offset`), and negative when
the field that failed began in an earlier chunk.
-/

namespace LeanMultipart

/-- What `QsParser.write` raises. -/
structure QsWriteError where
  error : QsError
  chunkOffset : Int
  deriving Repr, Inhabited

/-- Upstream's `QuerystringParser` object. -/
structure QsParser where
  cfg : QsConfig := {}
  st : QsState := {}
  deriving Inhabited

namespace QsParser

private def emitIf (evs : Array QsEvent) (b : Array UInt8) (mk : ByteArray → QsEvent) :
    Array QsEvent :=
  if b.size == 0 then evs else evs.push (mk ⟨b⟩)

/-- One byte: step the machine and fire the callbacks of the transition.
Only the old phase is kept, so the buffers are updated in place. -/
def stepEv (cfg : QsConfig) : QsState × Array QsEvent → UInt8 → QsState × Array QsEvent
  | (s, evs), c =>
  let ph := s.phase
  let s' := Qs.step cfg s c
  match ph, s'.phase with
  | .beforeField _, .fieldName => (s', evs.push .fieldStart)
  | .beforeField _, .fieldData => (s', evs.push .fieldStart)
  | .fieldName, .fieldData => ({ s' with name := #[] }, emitIf evs s'.name .fieldName)
  | .fieldName, .beforeField _ =>
    let f := s'.fields.back?.getD default
    ({ s' with fields := #[] }, (emitIf evs f.1.data .fieldName).push .fieldEnd)
  | .fieldData, .beforeField _ =>
    let f := s'.fields.back?.getD default
    ({ s' with fields := #[] }, (emitIf evs f.2.data .fieldData).push .fieldEnd)
  | _, _ => (s', evs)

/-- End of a chunk: report the buffered part of the field in progress. -/
def flush (s : QsState) (evs : Array QsEvent) : QsState × Array QsEvent :=
  match s.phase with
  | .fieldName => ({ s with name := #[] }, emitIf evs s.name .fieldName)
  | .fieldData => ({ s with value := #[] }, emitIf evs s.value .fieldData)
  | _ => (s, evs)

def new (cfg : QsConfig := {}) : QsParser := { cfg }

/-- The state after a chunk, without the events. -/
def writeSt (p : QsParser) (chunk : Bytes) : QsState :=
  (flush ((chunk.take (Qs.room p.cfg p.st chunk.length)).foldl (stepEv p.cfg) (p.st, #[])).1 #[]).1

/-- Upstream's `write`: feed a chunk; get the callbacks fired and the number
of bytes processed (fewer than the chunk only under `maxSize`), or the
error. -/
def write (p : QsParser) (chunk : ByteArray) : Except QsWriteError (QsParser × Array QsEvent × Nat) :=
  let n := Qs.room p.cfg p.st chunk.size
  let (s, evs) := (chunk.data.extract 0 n).foldl (stepEv p.cfg) (p.st, #[])
  let (s, evs) := flush s evs
  match s.phase with
  | .failed e => .error ⟨e, (e.offset : Int) - p.st.pos⟩
  | _ => .ok ({ p with st := s }, evs, n)

/-- Upstream's `finalize`: close a field in progress, then `end`. -/
def finalize (p : QsParser) : Except QsError (Array QsEvent) :=
  match p.st.phase with
  | .failed e => .error e
  | .fieldName | .fieldData => .ok (#[QsEvent.fieldEnd, .end])
  | _ => .ok #[.end]

end QsParser

end LeanMultipart
