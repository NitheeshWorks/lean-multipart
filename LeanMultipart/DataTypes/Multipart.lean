import LeanMultipart.DataTypes.Boundary

/-!
# Multipart parser types

The state of the byte-at-a-time multipart state machine, its configuration,
its errors and the callback events it emits. The phases mirror upstream's
`MultipartState` (`START`, `START_BOUNDARY`, `HEADER_FIELD_START`, ...), with
one extra phase, `preamble`, that remembers across chunks that the parser is
skipping a preamble (see `CONTRIBUTING.md`, deviations).
-/

namespace LeanMultipart

/-- One part as the `MultipartParser` sees it: its headers in order (names as
sent, not lower-cased) and its body bytes. -/
structure RawPart where
  headers : List (ByteArray × ByteArray)
  body : ByteArray
  deriving Inhabited

/-- Upstream's `MultipartParser` limits (`max_size`, `max_header_count`,
`max_header_size`). `maxSize = none` is upstream's `float("inf")`. -/
structure MultipartConfig where
  maxSize : Option Nat := none
  maxHeaderCount : Nat := 8
  maxHeaderSize : Nat := 4096 + 128
  /-- Upstream rejects `max_size < 1`. -/
  h_maxSize : ∀ m, maxSize = some m → 0 < m := by intro m h; cases h <;> decide

instance : Inhabited MultipartConfig := ⟨{}⟩

/-- What went wrong, and the absolute byte offset where it was detected. The
kinds correspond one-to-one to the messages of upstream's
`MultipartParseError`. -/
inductive MultipartErrorKind where
  /-- "Expected boundary character %r, got %r" -/
  | expectedBoundaryChar
  /-- "Did not find CR at end of boundary" -/
  | noCRAfterBoundary
  /-- "Did not find LF at end of boundary" -/
  | noLFAfterBoundary
  /-- "Did not find - at end of boundary" -/
  | noHyphenAfterBoundary
  /-- "Maximum header count exceeded" -/
  | headerCountExceeded
  /-- "Maximum header size exceeded" -/
  | headerSizeExceeded
  /-- "Found 0-length header" -/
  | emptyHeaderName
  /-- "Found invalid character %r in header" -/
  | invalidHeaderChar
  /-- "Did not find LF character at end of header" -/
  | noLFAfterHeader
  /-- "Did not find LF at end of headers" -/
  | noLFAfterHeaders
  deriving DecidableEq, Repr, Inhabited

structure MultipartError where
  kind : MultipartErrorKind
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Progress through the delimiter while scanning part data: `idx k` means
the last `k` bytes seen are the first `k` bytes of the delimiter (`k = 0`:
none); `afterD` means the whole delimiter has been seen; `afterDCR` and
`afterDHyphen` mean it was followed by `CR` or `-`. -/
inductive DelimMatch where
  | idx (k : Nat)
  | afterD
  | afterDCR
  | afterDHyphen
  deriving DecidableEq, Repr, Inhabited

/-- The parser's phase. -/
inductive MPhase where
  | start
  | preamble
  | startBoundary (k : Nat)
  | startBoundaryCR
  | endBoundary
  | headerFieldStart
  | headerField
  | headerValueStart
  | headerValue
  | headerValueAlmostDone
  | headersAlmostDone
  | partData (m : DelimMatch)
  | done
  | failed (e : MultipartError)
  deriving DecidableEq, Repr, Inhabited

/-- The full state of the multipart state machine. `data` holds the current
part's body bytes that are known not to belong to a delimiter; the bytes of
a partial delimiter match are implied by `phase`. `pos` counts every byte
fed so far. -/
structure MState where
  phase : MPhase := .start
  pos : Nat := 0
  hdrCount : Nat := 0
  hdrSize : Nat := 0
  name : Array UInt8 := #[]
  value : Array UInt8 := #[]
  headers : Array (ByteArray × ByteArray) := #[]
  data : Array UInt8 := #[]
  parts : Array RawPart := #[]
  deriving Inhabited

/-- The callbacks of upstream's `MultipartParser`, as data. `partData`,
`headerField` and `headerValue` carry the bytes upstream passes as
`(data, start, end)`. -/
inductive MultipartEvent where
  | partBegin
  | headerBegin
  | headerField (b : ByteArray)
  | headerValue (b : ByteArray)
  | headerEnd
  | headersFinished
  | partData (b : ByteArray)
  | partEnd
  | «end»
  deriving Inhabited

/-- The outcome of feeding a whole body: the completed parts, the part being
read when the input ran out (if its headers were complete), whether the
closing delimiter was seen, the first error, and how many bytes were
processed (after `maxSize` truncation). -/
structure MultipartResult where
  parts : List RawPart
  current : Option RawPart
  ended : Bool
  error : Option MultipartError
  processed : Nat
  deriving Inhabited

end LeanMultipart
