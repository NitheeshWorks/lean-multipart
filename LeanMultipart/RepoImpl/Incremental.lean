import LeanMultipart.RepoImpl.Form
import LeanMultipart.RepoImpl.MpStream
import LeanMultipart.RepoImpl.DelimRun

/-!
# Starlette's multipart parser, incremental

Starlette's `MultiPartParser.parse` feeds the request stream to
python-multipart's `MultipartParser` chunk by chunk, and its callbacks do
three things with what they are told: at `on_headers_finished` they read the
part's `name` and `filename` and count it against `max_fields` or
`max_files`; at `on_part_data` they append a field's bytes (checked against
`max_part_size`) or hand a file's bytes to its spool; at `on_part_end` they
close the part. `MultipartStream` is that, as a pure state machine fed
chunks:

```lean
let p ← Starlette.MultipartStream.create contentType lim   -- or `.new boundary lim`
-- for each chunk read from the transport:
match p.feed chunk with
| .error e => -- Starlette's MultiPartException (close the spooled files)
| .ok (p', events) =>
  for ev in events do
    match ev with
    | .part info => -- a new part: info.name, info.filename, info.headers
    | .data bytes => -- the next bytes of the current part
    | .partEnd => -- the current part is complete
```

A part that has a `.part` event and no `.partEnd` when the stream ends is
not in the form (Starlette never calls `on_part_end` for it). Nothing has to
be done at the end of the stream: python-multipart's `finalize` does nothing.

Between chunks the parser keeps only the delimiter progress, the headers of
the current part (bounded by `max_header_count` and `max_header_size`) and
four counters; every data byte of a chunk is reported in that chunk's
events, except the bytes that may begin a delimiter, which are implied by
the phase (`Starlette.feed_retains`). `Starlette.MultipartStream.parseChunks_eq`
proves that, for every split of the body into chunks, the parts assembled
from the events are the parts of the whole-buffer parse
(`Starlette.parseMultipartRaw`), or its error.

The step is python-multipart's (`MultipartParser.stepEv`) with Starlette's
checks on its transitions, made at the byte where Starlette's callbacks
make them. A run of part data is taken at once (`Mp.dataSpan`), cut for a
field part before the byte that would cross `max_part_size`.
-/

namespace LeanMultipart
namespace Starlette

/-- What Starlette reads off a part when its headers end
(`on_headers_finished`): the `name` and `filename` parameters of its
`Content-Disposition`, and its headers with lower-cased names, in order. -/
structure PartInfo where
  name : ByteArray
  filename : Option ByteArray
  headers : List (ByteArray × ByteArray)
  deriving Inhabited

/-- Whether the part is a file (it has a `filename`). -/
def PartInfo.isFile (i : PartInfo) : Bool := i.filename.isSome

/-- The part, with its data. -/
def PartInfo.toPart (i : PartInfo) (data : ByteArray) : StarlettePart :=
  { name := i.name, filename := i.filename, headers := i.headers, data }

/-- The part info of headers whose `Content-Disposition` has this `name` and
`filename`, as `partOf` builds it. -/
def PartInfo.ofHeaders (hs : List (ByteArray × ByteArray)) (name : Bytes) (filename : Option Bytes) : PartInfo :=
  { name := ⟨name.toArray⟩, filename := filename.map (fun f => ⟨f.toArray⟩),
    headers := hs.map (fun h => (lowerAscii h.1, h.2)) }

/-- What the incremental parser reports: a part begins (its headers are
complete and within the limits), a piece of its data, its end. -/
inductive PartEvent where
  | part (info : PartInfo)
  | data (b : ByteArray)
  | partEnd
  deriving Inhabited

/-- The parser's state: python-multipart's (with what has been reported
forgotten), the counts of files and fields, whether the current part is a
file, how many of its data bytes have been reported, and the first error. -/
structure PState where
  mp : MState := {}
  nFiles : Nat := 0
  nFields : Nat := 0
  curIsFile : Bool := false
  sent : Nat := 0
  err : Option LimitError := none
  deriving Inhabited

/-- After a limit error, a parse error or the closing delimiter nothing more
is read. -/
def PState.halted (s : PState) : Bool :=
  s.err.isSome || (match s.mp.phase with | .failed _ | .done => true | _ => false)

/-- The part data and part end of python-multipart's events; the rest are
read off the state. -/
def ofMpEvent : MultipartEvent → Option PartEvent
  | .partData b => some (.data b)
  | .partEnd => some .partEnd
  | _ => none

/-- One byte: python-multipart's step, then Starlette's checks on its
transition. -/
def pStep (cx : Mp.Ctx) (lim : FormLimits) : PState × Array PartEvent → UInt8 → PState × Array PartEvent
  | (s, out), c =>
  if s.halted then (s, out) else
  -- `s` is taken apart first, so python-multipart's state is stepped in place.
  let ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  let ph := mp.phase
  let (m', evs) := MultipartParser.stepEv cx (mp, #[]) c
  let out := if evs.isEmpty then out else out ++ evs.filterMap ofMpEvent
  match ph, m'.phase with
  | .headersAlmostDone, .partData _ =>
    let hs := m'.headers.toList
    match dispositionParams hs with
    | (none, _) => (⟨m', nFiles, nFields, curIsFile, sent, some .missingName⟩, out)
    | (some n, some f) =>
      if lim.maxFiles < nFiles + 1 then (⟨m', nFiles, nFields, curIsFile, sent, some (.tooManyFiles lim.maxFiles)⟩, out)
      else (⟨m', nFiles + 1, nFields, true, 0, err⟩, out.push (.part (PartInfo.ofHeaders hs n (some f))))
    | (some n, none) =>
      if lim.maxFields < nFields + 1 then (⟨m', nFiles, nFields, curIsFile, sent, some (.tooManyFields lim.maxFields)⟩, out)
      else (⟨m', nFiles, nFields + 1, false, 0, err⟩, out.push (.part (PartInfo.ofHeaders hs n none)))
  | .partData _, .partData _ =>
    if !curIsFile && lim.maxPartSize < sent + m'.data.size then
      (⟨m', nFiles, nFields, curIsFile, sent, some (.partTooLarge lim.maxPartSize)⟩, out)
    else (⟨m', nFiles, nFields, curIsFile, sent, err⟩, out)
  | _, _ => (⟨m', nFiles, nFields, curIsFile, sent, err⟩, out)

/-- Where a run of data may end: for a field part, far enough before
`max_part_size` that the run (and the pending match it resolves, shorter
than the delimiter) cannot cross it; the bytes near the limit are stepped
one at a time. -/
def pStop (cx : Mp.Ctx) (lim : FormLimits) (s : PState) (i stop : Nat) : Nat :=
  if s.curIsFile then stop else min stop (i + (lim.maxPartSize - (s.sent + s.mp.data.size + cx.dlen)))

def pSpan (cx : Mp.Ctx) (lim : FormLimits) (r : PState × Array PartEvent) (b : ByteArray) (i stop : Nat) : Nat :=
  if r.1.err.isSome then 0 else Mp.runSpan cx r.1.mp b i (pStop cx lim r.1 i stop)

def pBulk (cx : Mp.Ctx) : PState × Array PartEvent → ByteArray → Nat → Nat → PState × Array PartEvent
  | (⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out), b, i, n =>
    (⟨Mp.runBulk cx mp b i n, nFiles, nFields, curIsFile, sent, err⟩, out)

/-- End of a chunk: report the data of the current part read so far. -/
def pFlush : PState → Array PartEvent → PState × Array PartEvent
  | ⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out =>
    let d := mp.data
    let mp := { mp with data := ByteArray.empty }
    match mp.phase with
    | .partData _ => (⟨mp, nFiles, nFields, curIsFile, sent + d.size, err⟩, if d.size == 0 then out else out.push (.data d))
    | _ => (⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out)

/-- Fold a chunk's bytes, taking runs of data at once and stopping once halted. -/
def pChunk (cx : Mp.Ctx) (lim : FormLimits) (chunk : ByteArray) (r : PState × Array PartEvent) :
    PState × Array PartEvent :=
  bytesFoldRun (pStep cx lim) (pSpan cx lim) (pBulk cx) (fun r => r.1.halted) chunk chunk.size 0 r

/-- Starlette's `MultiPartParser`, fed chunks. -/
structure MultipartStream where
  cx : Mp.Ctx
  lim : FormLimits := {}
  st : PState := {}

namespace MultipartStream

/-- A parser for this boundary, under Starlette's limits (`max_files`,
`max_fields`, `max_part_size`; defaults 1000, 1000, 1 MiB). -/
def new (boundary : Boundary) (lim : FormLimits := {}) : MultipartStream := { cx := { boundary }, lim }

/-- A parser for a request's `Content-Type`: Starlette's "Missing boundary in
multipart." without a `boundary` parameter. A boundary python-multipart
would fail on (not a `Boundary`) is "Invalid multipart data.", as Starlette
reports that failure. -/
def create (contentType : ByteArray) (lim : FormLimits := {}) : Except LimitError MultipartStream :=
  match boundaryParam contentType with
  | none => .error .missingBoundary
  | some b =>
    match Boundary.ofBytes? ⟨b.toArray⟩ with
    | none => .error .invalidMultipart
    | some bd => .ok (new bd lim)

/-- Feed the next chunk of the body: the events it completes, or the error
Starlette raises (a parse error is "Invalid multipart data."). -/
def feed (p : MultipartStream) (chunk : ByteArray) : Except LimitError (MultipartStream × Array PartEvent) :=
  let (s, out) := pChunk p.cx p.lim chunk (p.st, #[])
  let (s, out) := pFlush s out
  match s.err with
  | some e => .error e
  | none =>
    match s.mp.phase with
    | .failed _ => .error .invalidMultipart
    | _ => .ok ({ p with st := s }, out)

/-- Whether the closing delimiter has been read (the rest of the body is the
epilogue, which is ignored). -/
def ended (p : MultipartStream) : Bool := p.st.mp.phase == .done

/-! ## Assembling the parts from the events -/

/-- What a consumer that keeps every part in memory does with the events. -/
structure Collector where
  done : Array StarlettePart := #[]
  cur : StarlettePart := default

def Collector.event (c : Collector) : PartEvent → Collector
  | .part info => { c with cur := info.toPart ByteArray.empty }
  | .data b => { c with cur := { c.cur with data := c.cur.data ++ b } }
  | .partEnd => { c with done := c.done.push c.cur }

def Collector.events (c : Collector) (evs : Array PartEvent) : Collector := evs.foldl Collector.event c

/-- Feed the chunks, assembling the parts the events report. -/
def collect (p : MultipartStream) (c : Collector) : List ByteArray → Except LimitError (List StarlettePart)
  | [] => .ok c.done.toList
  | chunk :: rest =>
    match p.feed chunk with
    | .error e => .error e
    | .ok (p', evs) => collect p' (c.events evs) rest

/-- Starlette's multipart form parse of a body that arrives in these chunks,
for a request with this `Content-Type`. -/
def parseChunks (lim : FormLimits) (contentType : ByteArray) (chunks : List ByteArray) :
    Except LimitError (List StarlettePart) := do
  let p ← create contentType lim
  collect p {} chunks

end MultipartStream

end Starlette
end LeanMultipart
