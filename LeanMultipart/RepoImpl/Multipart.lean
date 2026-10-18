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

/-! ## Runs of part data

In part data with no delimiter byte matched, every byte but `CR` (the
delimiter's first byte) is data, and `step` appends it. `dataSpan` finds
such a run and `dataBulk` appends it with one copy; `dataBulk_eq` proves that
is what `step` would do byte by byte, so `feedA` may take the shortcut. -/

theorem dAt_zero (cx : Ctx) : cx.dAt 0 = Byte.CR := by
  unfold Ctx.dAt; simp only [cx.h_delim, Boundary.delim, Boundary.delimL]
  rfl

/-- The length of the run of data bytes at `i`, before `stop` (0 if none). -/
def dataSpan (s : MState) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.phase with
  | .partData (.idx 0) => scanFor b Byte.CR stop i - i
  | _ => 0

/-- Append the `n` bytes at `i` to the part data. -/
def dataBulk (s : MState) (b : ByteArray) (i n : Nat) : MState :=
  if n = 0 then s else { s with pos := s.pos + n, data := b.copySlice i s.data s.data.size n false }

theorem step_data (cx : Ctx) (s : MState) (c : UInt8) (hs : s.phase = .partData (.idx 0))
    (hc : c ≠ Byte.CR) : step cx s c = { s with pos := s.pos + 1, data := s.data.push c } := by
  obtain ⟨ph, pos, hc', hs', n, v, hd, d, ps⟩ := s
  simp only at hs; subst hs
  simp [step, matchByte, dAt_zero, hc, restart]

theorem foldl_data (cx : Ctx) : ∀ (l : Bytes) (s : MState), s.phase = .partData (.idx 0) →
    (∀ x ∈ l, x ≠ Byte.CR) →
    l.foldl (step cx) s = { s with pos := s.pos + l.length, data := s.data ++ ⟨l.toArray⟩ } := by
  intro l
  induction l with
  | nil => intro s _ _; simp
  | cons c l ih =>
    intro s hs hl
    rw [List.foldl_cons, step_data cx s c hs (hl c (by simp)),
      ih { s with pos := s.pos + 1, data := s.data.push c } hs (fun x hx => hl x (by simp [hx]))]
    simp only [List.length_cons]
    congr 1
    · omega
    · apply ByteArray.ext_toList; simp [ByteArray.data_append]

theorem dataSpan_le (s : MState) (b : ByteArray) (i stop : Nat) : dataSpan s b i stop ≤ stop - i := by
  unfold dataSpan; split
  · rcases scanFor_le b Byte.CR stop _ i rfl with h | h <;> omega
  · exact Nat.zero_le _

theorem dataSpan_phase (s : MState) (b : ByteArray) (i stop : Nat) (h : dataSpan s b i stop ≠ 0) :
    s.phase = .partData (.idx 0) := by
  unfold dataSpan at h; split at h
  · assumption
  · exact absurd rfl h

theorem dataSpan_ne (s : MState) (b : ByteArray) (i stop : Nat) :
    ∀ x ∈ (b.data.toList.drop i).take (dataSpan s b i stop), x ≠ Byte.CR := by
  unfold dataSpan; split
  · exact scanFor_ne b Byte.CR stop _ i rfl
  · simp

/-- A run of data stays inside the input. -/
theorem dataSpan_size (s : MState) (b : ByteArray) (i stop : Nat) : i + dataSpan s b i stop ≤ b.size ∨ dataSpan s b i stop = 0 := by
  unfold dataSpan; split
  · rcases scanFor_le b Byte.CR stop _ i rfl with h | h <;> omega
  · exact Or.inr rfl

/-- Any prefix of a run, appended at once, is what `step` does. -/
theorem dataBulk_le (cx : Ctx) (s : MState) (b : ByteArray) (i stop k : Nat) (hk : k ≤ dataSpan s b i stop) :
    dataBulk s b i k = ((b.data.toList.drop i).take k).foldl (step cx) s := by
  unfold dataBulk
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    have hph := dataSpan_phase s b i stop (by omega)
    have hne : ∀ x ∈ (b.data.toList.drop i).take k, x ≠ Byte.CR := fun x hx =>
      dataSpan_ne s b i stop x (List.take_subset_take_left _ hk hx)
    have hlen : ((b.data.toList.drop i).take k).length = k := by
      rcases dataSpan_size s b i stop with hs | hs
      · simp [Array.length_toList]; omega
      · omega
    rw [foldl_data cx _ s hph hne, hlen, copySlice_end]
    congr 1
    apply ByteArray.ext_toList
    simp only [ByteArray.data_append, Array.toList_append, extract_toList]

theorem dataBulk_eq (cx : Ctx) (s : MState) (b : ByteArray) (i stop : Nat) :
    dataBulk s b i (dataSpan s b i stop) = ((b.data.toList.drop i).take (dataSpan s b i stop)).foldl (step cx) s :=
  dataBulk_le cx s b i stop _ (Nat.le_refl _)

/-- The machine: `step`, the byte counter, and the `maxSize` limit, with the
shortcut for runs of data. The general chunking theorems of
`Theory/Machine.lean` apply to it. -/
def machine (cx : Ctx) : Machine MState :=
  { step := step cx, pos := MState.pos, limit := cx.cfg.maxSize,
    span := dataSpan, bulk := dataBulk, span_le := dataSpan_le, bulk_eq := dataBulk_eq cx }

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
