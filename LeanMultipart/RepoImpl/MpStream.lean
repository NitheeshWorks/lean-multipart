import LeanMultipart.RepoImpl.Multipart

/-!
# `MultipartParser`

Upstream's streaming multipart parser:

```python
parser = MultipartParser(boundary, callbacks, max_size=…, max_header_count=8, max_header_size=4224)
parser.write(chunk)   # fires on_part_begin / on_header_field / ... / on_part_data / on_part_end / on_end
parser.finalize()
```

```lean
let p := MultipartParser.new boundary
let (p, events, n) ← p.write chunk
-- or with callbacks:
let (p, n) ← p.writeWith { onPartBegin := …, onPartData := fun b => …, onPartEnd := … } chunk
```

It runs the same `Mp.step` as the whole-buffer parser and forgets what it
has reported (completed parts, and part data reported at the end of each
chunk), so it streams a file in memory bounded by the chunk. Part data known
not to belong to a delimiter is reported at the end of each chunk, as
upstream does. Header names and values are reported whole when they end
(upstream may split them at chunk ends; the concatenation is the same).
-/

namespace LeanMultipart

/-- Upstream's `MultipartParseError`. -/
structure MultipartParseError where
  error : MultipartError
  /-- Offset in the chunk passed to this `write`. -/
  offset : Int
  deriving Inhabited

/-- Upstream's `MultipartCallbacks`, in any monad. -/
structure MultipartCallbacks (m : Type → Type) [Monad m] where
  onPartBegin : m Unit := pure ()
  onPartData : ByteArray → m Unit := fun _ => pure ()
  onPartEnd : m Unit := pure ()
  onHeaderBegin : m Unit := pure ()
  onHeaderField : ByteArray → m Unit := fun _ => pure ()
  onHeaderValue : ByteArray → m Unit := fun _ => pure ()
  onHeaderEnd : m Unit := pure ()
  onHeadersFinished : m Unit := pure ()
  onEnd : m Unit := pure ()

/-- Run a callback for an event. -/
def MultipartEvent.fire {m : Type → Type} [Monad m] (cb : MultipartCallbacks m) : MultipartEvent → m Unit
  | .partBegin => cb.onPartBegin
  | .headerBegin => cb.onHeaderBegin
  | .headerField b => cb.onHeaderField b
  | .headerValue b => cb.onHeaderValue b
  | .headerEnd => cb.onHeaderEnd
  | .headersFinished => cb.onHeadersFinished
  | .partData b => cb.onPartData b
  | .partEnd => cb.onPartEnd
  | .end => cb.onEnd

/-- Upstream's `MultipartParser` object. -/
structure MultipartParser where
  cx : Mp.Ctx
  st : MState := {}

namespace MultipartParser

def emitIf (evs : Array MultipartEvent) (b : ByteArray) (mk : ByteArray → MultipartEvent) :
    Array MultipartEvent :=
  if b.size == 0 then evs else evs.push (mk b)

def lastBody (s : MState) : ByteArray := (s.parts.back?.map (·.body)).getD ByteArray.empty

/-- One byte: step the machine and fire the callbacks of the transition. -/
def stepEv (cx : Mp.Ctx) : MState × Array MultipartEvent → UInt8 → MState × Array MultipartEvent
  | (s, evs), c =>
  let ph := s.phase
  let s' := Mp.step cx s c
  match ph, s'.phase with
  | .startBoundaryCR, .headerFieldStart => (s', evs.push .partBegin)
  | .headerFieldStart, .headerField => (s', evs.push .headerBegin)
  | .headerField, .headerValueStart => (s', evs.push (.headerField s'.name))
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

theorem stepEv_data (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8)
    (hs : s.phase = .partData (.idx 0)) (hc : c ≠ Byte.CR) :
    stepEv cx (s, evs) c = (Mp.step cx s c, evs) := by
  simp only [stepEv, Mp.step_data cx s c hs hc, hs]

theorem foldl_stepEv_data (cx : Mp.Ctx) : ∀ (l : Bytes) (s : MState) (evs : Array MultipartEvent),
    s.phase = .partData (.idx 0) → (∀ x ∈ l, x ≠ Byte.CR) →
    l.foldl (stepEv cx) (s, evs) = (l.foldl (Mp.step cx) s, evs) := by
  intro l
  induction l with
  | nil => intro _ _ _ _; rfl
  | cons c l ih =>
    intro s evs hs hl
    have hc := hl c (by simp)
    rw [List.foldl_cons, List.foldl_cons, stepEv_data cx s evs c hs hc]
    exact ih _ _ (by rw [Mp.step_data cx s c hs hc]; exact hs) (fun x hx => hl x (by simp [hx]))

/-- The data-run shortcut, with the events alongside (a run fires none). -/
def evSpan (r : MState × Array MultipartEvent) (b : ByteArray) (i stop : Nat) : Nat := Mp.dataSpan r.1 b i stop

def evBulk (r : MState × Array MultipartEvent) (b : ByteArray) (i n : Nat) : MState × Array MultipartEvent :=
  (Mp.dataBulk r.1 b i n, r.2)

theorem evBulk_eq (cx : Mp.Ctx) (r : MState × Array MultipartEvent) (b : ByteArray) (i stop : Nat) :
    evBulk r b i (evSpan r b i stop) = ((b.data.toList.drop i).take (evSpan r b i stop)).foldl (stepEv cx) r := by
  obtain ⟨s, evs⟩ := r
  unfold evBulk evSpan
  rw [Mp.dataBulk_eq cx]
  by_cases h : Mp.dataSpan s b i stop = 0
  · rw [h]; rfl
  · exact (foldl_stepEv_data cx _ s evs (Mp.dataSpan_phase s b i stop h) (Mp.dataSpan_ne s b i stop)).symm

/-- Fold a chunk's bytes, taking runs of data at once. -/
def foldChunk (cx : Mp.Ctx) (chunk : ByteArray) (n : Nat) (r : MState × Array MultipartEvent) :
    MState × Array MultipartEvent :=
  bytesFoldRun (stepEv cx) evSpan evBulk (fun _ => false) chunk n 0 r

theorem foldChunk_eq (cx : Mp.Ctx) (chunk : ByteArray) (n : Nat) (r : MState × Array MultipartEvent) :
    foldChunk cx chunk n r = bytesFold (stepEv cx) chunk n 0 r :=
  bytesFoldRun_eq (stepEv cx) evSpan evBulk (fun _ => false) (fun _ _ h => by cases h)
    (fun r b i stop => Mp.dataSpan_le r.1 b i stop) (evBulk_eq cx) chunk n _ 0 r rfl

/-- End of a chunk: report the part data known so far. -/
def flush (s : MState) (evs : Array MultipartEvent) : MState × Array MultipartEvent :=
  match s.phase with
  | .partData _ => ({ s with data := ByteArray.empty }, emitIf evs s.data .partData)
  | _ => (s, evs)

/-- A fresh parser: upstream's `MultipartParser(boundary, max_size=…,
max_header_count=…, max_header_size=…)`. -/
def new (boundary : Boundary) (cfg : MultipartConfig := {}) : MultipartParser :=
  { cx := { boundary, cfg } }

/-- Upstream's `write`: feed a chunk; get the callbacks fired, as events,
and the number of bytes processed, or the error. -/
def write (p : MultipartParser) (chunk : ByteArray) :
    Except MultipartParseError (MultipartParser × Array MultipartEvent × Nat) :=
  let n := Mp.room p.cx p.st chunk.size
  let (s, evs) := foldChunk p.cx chunk n (p.st, #[])
  let (s, evs) := flush s evs
  match s.phase with
  | .failed e => .error ⟨e, (e.offset : Int) - p.st.pos⟩
  | _ => .ok ({ p with st := s }, evs, n)

/-- `write`, firing callbacks. -/
def writeWith {m : Type → Type} [Monad m] (p : MultipartParser) (cb : MultipartCallbacks m)
    (chunk : ByteArray) : m (Except MultipartParseError (MultipartParser × Nat)) := do
  match p.write chunk with
  | .error e => pure (.error e)
  | .ok (p', evs, n) =>
    for e in evs do e.fire cb
    pure (.ok (p', n))

/-- Upstream's `finalize` does nothing and raises nothing. -/
def finalize (_p : MultipartParser) : Unit := ()

/-- Whether the closing delimiter has been seen. -/
def ended (p : MultipartParser) : Bool := p.st.phase == .done

/-! ## Collecting parts from the callbacks -/

/-- What upstream's `FormParser` does with the multipart callbacks: build
each part from its header and data pieces. -/
structure Collector where
  done : Array RawPart := #[]
  headers : Array (ByteArray × ByteArray) := #[]
  hname : ByteArray := ByteArray.empty
  hvalue : ByteArray := ByteArray.empty
  body : ByteArray := ByteArray.empty

def Collector.event (c : Collector) : MultipartEvent → Collector
  | .partBegin => { c with headers := #[], body := ByteArray.empty }
  | .headerBegin => { c with hname := ByteArray.empty, hvalue := ByteArray.empty }
  | .headerField b => { c with hname := c.hname ++ b }
  | .headerValue b => { c with hvalue := c.hvalue ++ b }
  | .headerEnd => { c with headers := c.headers.push (c.hname, c.hvalue) }
  | .headersFinished => c
  | .partData b => { c with body := c.body ++ b }
  | .partEnd => { c with done := c.done.push ⟨c.headers.toList, c.body⟩ }
  | .end => c

def Collector.events (c : Collector) (evs : Array MultipartEvent) : Collector := evs.foldl Collector.event c

/-- Feed the chunks to a fresh parser, collecting the parts its callbacks
report. -/
def parseChunks (cx : Mp.Ctx) (chunks : List ByteArray) : Except MultipartError (List RawPart) :=
  go { cx } {} chunks
where
  go (p : MultipartParser) (c : Collector) : List ByteArray → Except MultipartError (List RawPart)
    | [] => .ok c.done.toList
    | chunk :: rest => match p.write chunk with
      | .error e => .error e.error
      | .ok (p', evs, _) => go p' (c.events evs) rest

end MultipartParser

/-- The parts of a whole-buffer parse, or its error (the part in progress at
the end, which upstream never reports, is dropped). -/
def MultipartResult.toExcept (r : MultipartResult) : Except MultipartError (List RawPart) :=
  match r.error with
  | some e => .error e
  | none => .ok r.parts

end LeanMultipart
