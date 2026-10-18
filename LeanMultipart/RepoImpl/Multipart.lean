import LeanMultipart.DataTypes.Multipart
import LeanMultipart.Theory.Machine

/-!
# The multipart state machine

Upstream's `MultipartParser`, one byte at a time. `Mp.step` is the whole
machine. Feeding a chunk is `List.foldl step`, so feeding chunks one after
another is feeding their concatenation (`Mp.feedT_append`); this is how the
streaming parser and the whole-buffer parser are shown to agree.

Semantics, as upstream:

* Before the first boundary, leading `CR`/`LF` start a preamble that is
  skipped up to the first `-` (`test_multipart_parser_preamble_before_first_boundary`).
  Any other first byte must start `--boundary`.
* `--boundary` is followed by `CR LF` (a part) or `--` (an empty message).
* A part's headers are `name: value CR LF` lines ended by an empty line.
  Names are RFC 7230 tokens; leading spaces of values are skipped; at most
  `maxHeaderCount` headers per part, each at most `maxHeaderSize` bytes.
* Part data runs to the delimiter `CR LF -- boundary`, followed by `CR LF`
  (next part) or `--` (end). A delimiter followed by anything else is data.
* After the closing delimiter everything is ignored (the epilogue).
-/

namespace LeanMultipart
namespace Mp

/-- What the machine needs besides its state: the boundary and the limits,
and the delimiter `CR LF -- boundary`, computed once. -/
structure Ctx where
  boundary : Boundary
  cfg : MultipartConfig := {}
  delim : ByteArray := boundary.delim
  h_delim : delim = boundary.delim := by rfl

/-- Delimiter byte `k` (0 past the end, which a valid index never is). -/
def Ctx.dAt (cx : Ctx) (k : Nat) : UInt8 := if h : k < cx.delim.size then cx.delim[k] else 0

def Ctx.dlen (cx : Ctx) : Nat := cx.delim.size

def fail (s : MState) (k : MultipartErrorKind) (p : Nat) : MState :=
  { s with phase := .failed ⟨k, p⟩ }

/-- A new part begins: reset the per-part buffers. -/
def beginPart (s : MState) : MState :=
  { s with phase := .headerFieldStart, hdrCount := 0, hdrSize := 0, name := ByteArray.empty, value := ByteArray.empty,
           headers := #[], data := ByteArray.empty }

/-- The current part is complete. -/
def finishPart (s : MState) : MState :=
  { s with parts := s.parts.push ⟨s.headers.toList, s.data⟩, headers := #[], data := ByteArray.empty }

/-- A byte of the opening `--boundary`, `k` bytes of which are matched. -/
def sbByte (cx : Ctx) (k : Nat) (s : MState) (c : UInt8) (p : Nat) : MState :=
  if k + 2 < cx.dlen then
    if c == cx.dAt (k + 2) then { s with phase := .startBoundary (k + 1) }
    else fail s .expectedBoundaryChar p
  else if c == Byte.HYPHEN then { s with phase := .endBoundary }
  else if c == Byte.CR then { s with phase := .startBoundaryCR }
  else fail s .noCRAfterBoundary p

/-- A byte of a header name, or the colon that ends it. -/
def headerFieldByte (cx : Ctx) (s : MState) (c : UInt8) (p : Nat) : MState :=
  let z := s.hdrSize + 1
  if cx.cfg.maxHeaderSize < z then fail s .headerSizeExceeded p
  else if c == Byte.COLON then
    if s.name.isEmpty then fail s .emptyHeaderName p
    else { s with phase := .headerValueStart, hdrSize := z, value := ByteArray.empty }
  else if Byte.isTokenChar c then { s with phase := .headerField, hdrSize := z, name := s.name.push c }
  else fail s .invalidHeaderChar p

/-- A byte of a header value, or the `CR` that ends it. -/
def headerValueByte (cx : Ctx) (s : MState) (c : UInt8) (p : Nat) : MState :=
  if c == Byte.CR then
    { s with phase := .headerValueAlmostDone, headers := s.headers.push (s.name, s.value),
             name := ByteArray.empty, value := ByteArray.empty, hdrSize := 0 }
  else
    let z := s.hdrSize + 1
    if cx.cfg.maxHeaderSize < z then fail s .headerSizeExceeded p
    else { s with phase := .headerValue, hdrSize := z, value := s.value.push c }

/-- After a failed delimiter match the current byte is looked at afresh: a
`CR` may start a new match, anything else is data. -/
def restart (s : MState) (c : UInt8) : MState :=
  if c == Byte.CR then { s with phase := .partData (.idx 1) }
  else { s with phase := .partData (.idx 0), data := s.data.push c }

/-- A byte of part data, given the delimiter match so far. -/
def matchByte (cx : Ctx) (m : DelimMatch) (s : MState) (c : UInt8) : MState :=
  match m with
  | .idx k =>
    if c == cx.dAt k then
      if k + 1 == cx.dlen then { s with phase := .partData .afterD }
      else { s with phase := .partData (.idx (k + 1)) }
    else if k == 0 then restart s c
    else restart { s with data := s.data ++ cx.delim.extract 0 k } c
  | .afterD =>
    if c == Byte.CR then { s with phase := .partData .afterDCR }
    else if c == Byte.HYPHEN then { s with phase := .partData .afterDHyphen }
    else restart { s with data := s.data ++ cx.delim } c
  | .afterDCR =>
    if c == Byte.LF then beginPart (finishPart s)
    else restart { s with data := (s.data ++ cx.delim).push Byte.CR } c
  | .afterDHyphen =>
    if c == Byte.HYPHEN then { finishPart s with phase := .done }
    else restart { s with data := (s.data ++ cx.delim).push Byte.HYPHEN } c

/-- The transition function. Every byte advances `pos`. -/
def step (cx : Ctx) (s : MState) (c : UInt8) : MState :=
  let p := s.pos
  let s := { s with pos := p + 1 }
  match s.phase with
  | .failed _ => s
  | .done => s
  | .start => if c == Byte.CR || c == Byte.LF then { s with phase := .preamble } else sbByte cx 0 s c p
  | .preamble => if c == Byte.HYPHEN then sbByte cx 0 s c p else s
  | .startBoundary k => sbByte cx k s c p
  | .startBoundaryCR => if c == Byte.LF then beginPart s else fail s .noLFAfterBoundary p
  | .endBoundary => if c == Byte.HYPHEN then { s with phase := .done } else fail s .noHyphenAfterBoundary p
  | .headerFieldStart =>
    if c == Byte.CR then { s with phase := .headersAlmostDone }
    else
      let n := s.hdrCount + 1
      if cx.cfg.maxHeaderCount < n then fail s .headerCountExceeded p
      else headerFieldByte cx { s with hdrCount := n, hdrSize := 0, name := ByteArray.empty } c p
  | .headerField => headerFieldByte cx s c p
  | .headerValueStart =>
    if c == Byte.SPACE then
      if cx.cfg.maxHeaderSize < s.hdrSize + 1 then fail s .headerSizeExceeded p
      else { s with hdrSize := s.hdrSize + 1 }
    else headerValueByte cx s c p
  | .headerValue => headerValueByte cx s c p
  | .headerValueAlmostDone =>
    if c == Byte.LF then { s with phase := .headerFieldStart } else fail s .noLFAfterHeader p
  | .headersAlmostDone =>
    if c == Byte.LF then { s with phase := .partData (.idx 0), data := ByteArray.empty }
    else fail s .noLFAfterHeaders p
  | .partData m => matchByte cx m s c

/-- The machine: `step`, the byte counter, and the `maxSize` limit. The
general chunking theorems of `Theory/Machine.lean` apply to it. -/
def machine (cx : Ctx) : Machine MState := { step := step cx, pos := MState.pos, limit := cx.cfg.maxSize }

/-- Feed bytes (no truncation). -/
def feed (cx : Ctx) (s : MState) (l : Bytes) : MState := l.foldl (step cx) s

/-- How many more bytes `maxSize` allows. -/
def room (cx : Ctx) (s : MState) (n : Nat) : Nat :=
  match cx.cfg.maxSize with
  | none => n
  | some m => min n (m - s.pos)

/-- Feed bytes, truncated at `maxSize`. -/
def feedT (cx : Ctx) (s : MState) (l : Bytes) : MState :=
  feed cx s (l.take (room cx s l.length))

/-- Feeding chunks one after another, as `MultipartParser.write` does. -/
def feedChunks (cx : Ctx) (s : MState) (cs : List Bytes) : MState := (machine cx).feedChunks s cs

/-- Read the outcome off a state. -/
def result (s : MState) : MultipartResult where
  parts := s.parts.toList
  current := match s.phase with
    | .partData _ => some ⟨s.headers.toList, s.data⟩
    | _ => none
  ended := s.phase == .done
  error := match s.phase with
    | .failed e => some e
    | _ => none
  processed := s.pos

/-- The whole-buffer parser, on a list. -/
def parseL (cx : Ctx) (l : Bytes) : MultipartResult := result (feedT cx {} l)

/-- Feed a byte array, truncated at `maxSize`, as an array fold (no
intermediate list). Equal to `feedT` on the list (`Mp.feedA_eq`). -/
def feedA (cx : Ctx) (s : MState) (b : ByteArray) : MState :=
  (machine cx).feedA s b

/-- The whole-buffer parser. Equal to `parseL` on the bytes (`Mp.parse_eq`). -/
def parse (cx : Ctx) (body : ByteArray) : MultipartResult := result (feedA cx {} body)

/-! ## Printing -/

/-- `name: value CR LF`. -/
def headerLineL (h : ByteArray × ByteArray) : Bytes :=
  h.1.data.toList ++ [Byte.COLON, Byte.SPACE] ++ h.2.data.toList ++ [Byte.CR, Byte.LF]

/-- A part after its boundary line: header lines, an empty line, the body. -/
def partL (p : RawPart) : Bytes :=
  p.headers.flatMap headerLineL ++ [Byte.CR, Byte.LF] ++ p.body.data.toList

/-- The body of a `multipart/form-data` message with these parts: the
opening `--boundary CR LF`, each part followed by the delimiter
`CR LF --boundary` and separated by `CR LF`, then the closing `--` and
`CR LF`. An empty message is `--boundary-- CR LF`. -/
def printL (b : Boundary) : List RawPart → Bytes
  | [] => (b.delimL.drop 2 ++ [Byte.HYPHEN, Byte.HYPHEN]) ++ [Byte.CR, Byte.LF]
  | p :: rest =>
    (b.delimL.drop 2 ++ [Byte.CR, Byte.LF]) ++
      ((partL p ++ b.delimL) ++ rest.flatMap (fun q => [Byte.CR, Byte.LF] ++ (partL q ++ b.delimL))) ++
      [Byte.HYPHEN, Byte.HYPHEN] ++ [Byte.CR, Byte.LF]

def print (b : Boundary) (ps : List RawPart) : ByteArray := ⟨(printL b ps).toArray⟩

end Mp

end LeanMultipart
