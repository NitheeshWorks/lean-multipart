import LeanMultipart.RepoImpl.Querystring

/-!
# `QuerystringParser`

Upstream's streaming querystring parser:

```python
parser = QuerystringParser(callbacks, strict_parsing=False, max_size=float("inf"))
parser.write(chunk)     # fires on_field_start / on_field_name / on_field_data / on_field_end
parser.finalize()       # fires on_field_end for a field in progress, then on_end
```

```lean
let p := QuerystringParser.new (strictParsing := false)
let (p, events, n) ← p.write chunk      -- events: QsEvent.fieldStart, .fieldName b, ...
let events ← p.finalize
-- or, with callbacks in any monad:
let (p, n) ← p.writeWith callbacks chunk
```

It runs the same `Qs.step` as the whole-buffer parser and forgets what it
has reported (completed fields, and name or value bytes reported at the end
of a chunk), so it streams in memory bounded by the chunk. A failed write
returns `QuerystringParseError`, whose `offset` is relative to the chunk as
upstream's is; `error.offset` is the absolute stream offset.
-/

namespace LeanMultipart

/-- Upstream's `QuerystringParseError`. -/
structure QuerystringParseError where
  error : QsError
  /-- Offset in the chunk passed to this `write` (negative when the field at
  fault began in an earlier chunk). -/
  offset : Int
  deriving Inhabited

/-- Upstream's `QuerystringCallbacks`, in any monad. Missing callbacks do
nothing, as upstream's do. -/
structure QuerystringCallbacks (m : Type → Type) [Monad m] where
  onFieldStart : m Unit := pure ()
  onFieldName : ByteArray → m Unit := fun _ => pure ()
  onFieldData : ByteArray → m Unit := fun _ => pure ()
  onFieldEnd : m Unit := pure ()
  onEnd : m Unit := pure ()

/-- Run a callback for an event. -/
def QsEvent.fire {m : Type → Type} [Monad m] (cb : QuerystringCallbacks m) : QsEvent → m Unit
  | .fieldStart => cb.onFieldStart
  | .fieldName b => cb.onFieldName b
  | .fieldData b => cb.onFieldData b
  | .fieldEnd => cb.onFieldEnd
  | .end => cb.onEnd

/-- Upstream's `QuerystringParser` object. -/
structure QuerystringParser where
  cfg : QsConfig := {}
  st : QsState := {}
  deriving Inhabited

namespace QuerystringParser

def emitIf (evs : Array QsEvent) (b : ByteArray) (mk : ByteArray → QsEvent) :
    Array QsEvent :=
  if b.size == 0 then evs else evs.push (mk b)

/-- One byte: step the machine and fire the callbacks of the transition.
Only the old phase is kept, so the buffers are updated in place. -/
def stepEv (cfg : QsConfig) : QsState × Array QsEvent → UInt8 → QsState × Array QsEvent
  | (s, evs), c =>
  let ph := s.phase
  let s' := Qs.step cfg s c
  match ph, s'.phase with
  | .beforeField _, .fieldName => (s', evs.push .fieldStart)
  | .beforeField _, .fieldData => (s', evs.push .fieldStart)
  | .fieldName, .fieldData => ({ s' with name := ByteArray.empty }, emitIf evs s'.name .fieldName)
  | .fieldName, .beforeField _ =>
    let f := s'.fields.back?.getD default
    ({ s' with fields := #[] }, (emitIf evs f.1 .fieldName).push .fieldEnd)
  | .fieldData, .beforeField _ =>
    let f := s'.fields.back?.getD default
    ({ s' with fields := #[] }, (emitIf evs f.2 .fieldData).push .fieldEnd)
  | _, _ => (s', evs)

/-- End of a chunk: report the buffered part of the field in progress. -/
def flush (s : QsState) (evs : Array QsEvent) : QsState × Array QsEvent :=
  match s.phase with
  | .fieldName => ({ s with name := ByteArray.empty }, emitIf evs s.name .fieldName)
  | .fieldData => ({ s with value := ByteArray.empty }, emitIf evs s.value .fieldData)
  | _ => (s, evs)

/-- A fresh parser: upstream's `QuerystringParser(strict_parsing=…,
max_size=…)`. `maxSize` must be at least 1, as upstream requires. -/
def new (strictParsing : Bool := false) (maxSize : Option Nat := none)
    (h : ∀ m, maxSize = some m → 0 < m := by intro m h; cases h <;> decide) : QuerystringParser :=
  { cfg := { strictParsing := strictParsing, maxSize, h_maxSize := h } }

/-- Upstream's `write`: feed a chunk; get the callbacks fired, as events,
and the number of bytes processed (fewer than the chunk only under
`maxSize`), or the error. -/
def write (p : QuerystringParser) (chunk : ByteArray) :
    Except QuerystringParseError (QuerystringParser × Array QsEvent × Nat) :=
  let n := Qs.room p.cfg p.st chunk.size
  let (s, evs) := bytesFold (stepEv p.cfg) chunk n 0 (p.st, #[])
  let (s, evs) := flush s evs
  match s.phase with
  | .failed e => .error ⟨e, (e.offset : Int) - p.st.pos⟩
  | _ => .ok ({ p with st := s }, evs, n)

/-- Upstream's `finalize`: close a field in progress, then `end`. -/
def finalize (p : QuerystringParser) : Except QsError (Array QsEvent) :=
  match p.st.phase with
  | .failed e => .error e
  | .fieldName | .fieldData => .ok #[QsEvent.fieldEnd, .end]
  | _ => .ok #[.end]

/-- `write`, firing callbacks. -/
def writeWith {m : Type → Type} [Monad m] (p : QuerystringParser) (cb : QuerystringCallbacks m)
    (chunk : ByteArray) : m (Except QuerystringParseError (QuerystringParser × Nat)) := do
  match p.write chunk with
  | .error e => pure (.error e)
  | .ok (p', evs, n) =>
    for e in evs do e.fire cb
    pure (.ok (p', n))

/-- `finalize`, firing callbacks. -/
def finalizeWith {m : Type → Type} [Monad m] (p : QuerystringParser) (cb : QuerystringCallbacks m) :
    m (Except QsError Unit) := do
  match p.finalize with
  | .error e => pure (.error e)
  | .ok evs =>
    for e in evs do e.fire cb
    pure (.ok ())

/-! ## Collecting fields from the callbacks -/

/-- What upstream's `FormParser` does with the querystring callbacks: build
each field from its name and data pieces. -/
structure Collector where
  done : Array QsField := #[]
  name : ByteArray := ByteArray.empty
  value : ByteArray := ByteArray.empty

def Collector.event (c : Collector) : QsEvent → Collector
  | .fieldStart => { c with name := ByteArray.empty, value := ByteArray.empty }
  | .fieldName b => { c with name := c.name ++ b }
  | .fieldData b => { c with value := c.value ++ b }
  | .fieldEnd => { c with done := c.done.push (c.name, c.value) }
  | .end => c

def Collector.events (c : Collector) (evs : Array QsEvent) : Collector := evs.foldl Collector.event c

/-- Feed the chunks to a fresh parser, then finalize, collecting the fields
the callbacks report. -/
def parseChunks (cfg : QsConfig) (chunks : List ByteArray) : Except QsError (List QsField) :=
  go { cfg } {} chunks
where
  go (p : QuerystringParser) (c : Collector) : List ByteArray → Except QsError (List QsField)
    | [] => match p.finalize with
      | .error e => .error e
      | .ok evs => .ok (c.events evs).done.toList
    | chunk :: rest => match p.write chunk with
      | .error e => .error e.error
      | .ok (p', evs, _) => go p' (c.events evs) rest

end QuerystringParser

end LeanMultipart
