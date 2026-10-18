import LeanMultipart.RepoImpl.Multipart

/-!
# The callback-style multipart parser

Upstream's `MultipartParser` object, emitting the callbacks as
`MultipartEvent`s. It runs the same `Mp.step` as the whole-buffer parser
and forgets what it has reported: completed parts, and part data flushed at
the end of a chunk, so it streams a file in memory bounded by the chunk.
`Proofs/Stream.lean` proves its state is the whole-buffer state with those
buffers cleared (`MultipartParser.st_writeAll`).

Part data known not to belong to a delimiter is reported at the end of
each chunk, as upstream does. Header names and values are reported whole
when they end (upstream may split them at chunk ends; the concatenation is
the same).
-/

namespace LeanMultipart

/-- What `MultipartParser.write` raises: the error, with its offset also
relative to this chunk (upstream's `offset`). -/
structure MultipartWriteError where
  error : MultipartError
  chunkOffset : Int
  deriving Repr, Inhabited

/-- Upstream's `MultipartParser` object. -/
structure MultipartParser where
  cx : Mp.Ctx
  st : MState := {}

namespace MultipartParser

private def emitIf (evs : Array MultipartEvent) (b : ByteArray) (mk : ByteArray → MultipartEvent) :
    Array MultipartEvent :=
  if b.size == 0 then evs else evs.push (mk b)

private def lastBody (s : MState) : ByteArray := (s.parts.back?.map (·.body)).getD ByteArray.empty

/-- One byte: step the machine and fire the callbacks of the transition.
Only the old phase is kept, so the buffers are updated in place. -/
def stepEv (cx : Mp.Ctx) : MState × Array MultipartEvent → UInt8 →
    MState × Array MultipartEvent
  | (s, evs), c =>
  let ph := s.phase
  let s' := Mp.step cx s c
  match ph, s'.phase with
  | .startBoundaryCR, .headerFieldStart => (s', evs.push .partBegin)
  | .headerFieldStart, .headerField => (s', evs.push .headerBegin)
  | .headerField, .headerValueStart => (s', evs.push (.headerField ⟨s'.name⟩))
  | .headerValueStart, .headerValueAlmostDone =>
    (s', (emitIf evs ((s'.headers.back?.map (·.2)).getD ByteArray.empty) .headerValue).push .headerEnd)
  | .headerValue, .headerValueAlmostDone =>
    (s', (emitIf evs ((s'.headers.back?.map (·.2)).getD ByteArray.empty) .headerValue).push .headerEnd)
  | .headersAlmostDone, .partData _ => (s', evs.push .headersFinished)
  | .partData _, .headerFieldStart =>
    ({ s' with parts := #[] }, (((emitIf evs (lastBody s') .partData).push .partEnd).push .partBegin))
  | .partData _, .done =>
    ({ s' with parts := #[] }, (((emitIf evs (lastBody s') .partData).push .partEnd).push MultipartEvent.end))
  | .endBoundary, .done => (s', evs.push MultipartEvent.end)
  | _, _ => (s', evs)

/-- End of a chunk: report the part data known so far. -/
def flush (s : MState) (evs : Array MultipartEvent) : MState × Array MultipartEvent :=
  match s.phase with
  | .partData _ => ({ s with data := #[] }, emitIf evs ⟨s.data⟩ .partData)
  | _ => (s, evs)

/-- A fresh parser for a boundary. -/
def new (boundary : Boundary) (cfg : MultipartConfig := {}) : MultipartParser :=
  { cx := { boundary, cfg } }

/-- The state after a chunk, without the events. -/
def writeSt (p : MultipartParser) (chunk : Bytes) : MState :=
  (flush ((chunk.take (Mp.room p.cx p.st chunk.length)).foldl (stepEv p.cx) (p.st, #[])).1 #[]).1

/-- Upstream's `write`: feed a chunk; get the callbacks fired and the number
of bytes processed (fewer than the chunk only under `maxSize`), or the
error. -/
def write (p : MultipartParser) (chunk : ByteArray) :
    Except MultipartWriteError (MultipartParser × Array MultipartEvent × Nat) :=
  let n := Mp.room p.cx p.st chunk.size
  let (s, evs) := (chunk.data.extract 0 n).foldl (stepEv p.cx) (p.st, #[])
  let (s, evs) := flush s evs
  match s.phase with
  | .failed e => .error ⟨e, (e.offset : Int) - p.st.pos⟩
  | _ => .ok ({ p with st := s }, evs, n)

/-- Upstream's `finalize` does nothing and raises nothing. -/
def finalize (_p : MultipartParser) : Array MultipartEvent := #[]

/-- Whether the closing delimiter has been seen. -/
def ended (p : MultipartParser) : Bool := p.st.phase == .done

end MultipartParser

end LeanMultipart
