import LeanMultipart.RepoImpl.Form
import LeanMultipart.RepoImpl.MpStream

/-!
# The parsers as `IO` objects

Upstream's parsers are mutable objects that raise on errors, and
`parse_form` reads from a file-like stream. This file gives the same shape
in `IO` on top of the pure parsers, so code reads like upstream's:

```lean
let parser ← MultipartParser.create boundary callbacks
parser.write data          -- raises a `MultipartParseError` as an `IO` error
parseFormStream headers inputStream onField onFile
```

Nothing here is proved; each function is a thin loop over a pure parser
whose theorems are in `Proofs/`.
-/

namespace LeanMultipart

/-- Upstream's error message. -/
def MultipartErrorKind.message : MultipartErrorKind → String
  | .expectedBoundaryChar => "Expected boundary character"
  | .noCRAfterBoundary => "Did not find CR at end of boundary"
  | .noLFAfterBoundary => "Did not find LF at end of boundary"
  | .noHyphenAfterBoundary => "Did not find - at end of boundary"
  | .headerCountExceeded => "Maximum header count exceeded"
  | .headerSizeExceeded => "Maximum header size exceeded"
  | .emptyHeaderName => "Found 0-length header"
  | .invalidHeaderChar => "Found invalid character in header"
  | .noLFAfterHeader => "Did not find LF character at end of header"
  | .noLFAfterHeaders => "Did not find LF at end of headers"

instance : ToString MultipartParseError where
  toString e := s!"MultipartParseError: {e.error.kind.message} at {e.offset}"

/-- Python's `repr` of a byte string, as in `b'x'`. -/
def pyBytesRepr (b : ByteArray) : String :=
  let q : Char := if b.data.contains 39 && !b.data.contains 34 then '"' else '\''
  let hex (n : Nat) : Char := "0123456789abcdef".toList[n]!
  let esc (c : UInt8) : String :=
    if c == 9 then "\\t" else if c == 10 then "\\n" else if c == 13 then "\\r"
    else if c == 92 then "\\\\"
    else if c == 39 && q == '\'' then "\\'"
    else if 32 ≤ c && c < 127 then String.singleton (Char.ofNat c.toNat)
    else String.ofList ['\\', 'x', hex (c.toNat / 16), hex (c.toNat % 16)]
  "b" ++ String.singleton q ++ String.join (b.data.toList.map esc) ++ String.singleton q

instance : ToString FormError where
  toString
    | .multipart e => s!"MultipartParseError: {e.kind.message} at {e.offset}"
    | .querystring e => s!"QuerystringParseError: {match e.kind with
        | .duplicateAmpersand => "Skipping duplicate ampersand"
        | .missingEquals => "When strict_parsing is True, we require an equals sign in all field chunks"} (offset {e.offset})"
    | .noBoundary => "FormParserError: No boundary given"
    | .badBoundary => "FormParserError: Invalid boundary"
    | .unknownContentType ct => s!"FormParserError: Unknown Content-Type: {ct}"
    | .noContentType => "ValueError: No Content-Type header given!"
    | .badContentLength v => s!"ValueError: invalid literal for int() with base 10: {pyBytesRepr v}"
    | .negativeContentLength => "ValueError: Content-Length must be non-negative"
    | .missingFieldName => "FormParserError: Field name not found in Content-Disposition"
    | .badCte _ => "FormParserError: Unknown Content-Transfer-Encoding"
    | .decode _ => "DecodeError: invalid base64 data"

/-- A `MultipartParser` with its callbacks, as upstream's mutable object. -/
structure MultipartParser.Object where
  parser : IO.Ref MultipartParser
  callbacks : MultipartCallbacks IO

/-- Upstream's `MultipartParser(boundary, callbacks)`. The boundary is the
`params.get(b"boundary")` of `parse_options_header`, so it may be missing:
then this raises upstream's `TypeError` (its constructor takes `len(None)`). A boundary that is not a `Boundary` (1 to 256 RFC 2046
`bchars`; CONTRIBUTING deviation 4) raises a `ValueError` here, where
upstream accepts any bytes, `b''` included, and fails only at `write`. -/
def MultipartParser.create (boundary : Option ByteArray) (callbacks : MultipartCallbacks IO := {})
    (config : MultipartConfig := {}) : IO MultipartParser.Object := do
  let some b := boundary | throw (IO.userError "TypeError: object of type 'NoneType' has no len()")
  let some bd := Boundary.ofBytes? b |
    throw (IO.userError s!"ValueError: invalid boundary {pyBytesRepr b}: a boundary has 1 to 256 RFC 2046 bchars")
  return { parser := ← IO.mkRef (MultipartParser.new bd config), callbacks }

namespace MultipartParser.Object

/-- Upstream's `write(data)`: run the callbacks for this chunk and return the
number of bytes processed, or raise the parse error. -/
def write (p : MultipartParser.Object) (data : ByteArray) : IO Nat := do
  match ← (← p.parser.get).writeWith p.callbacks data with
  | .error e => throw (IO.userError (toString e))
  | .ok (q, n) => p.parser.set q; return n

/-- Upstream's `finalize()`, which does nothing for a multipart parser. -/
def finalize (_p : MultipartParser.Object) : IO Unit := pure ()

end MultipartParser.Object

/-- Upstream's `parse_form(headers, input_stream, on_field, on_file,
chunk_size)`: read the body in chunks of `chunkSize`, never past
`Content-Length` (read as Python's `int()` reads it), write each to the
parser, then call `onField` / `onFile` for each field and file in order.
Errors are raised as `IO` errors with upstream's class and message.

The callbacks run once the whole body is read (CONTRIBUTING deviation 6):
when the body has an error, none runs, where upstream calls them for the
items before the error and then raises. -/
def parseFormStream (headers : Headers) (inputStream : IO.FS.Stream) (onField : Field → IO Unit)
    (onFile : File → IO Unit) (chunkSize : Nat := 1048576) (config : FormParserConfig := {}) : IO Unit := do
  if chunkSize < 1 then throw (IO.userError s!"ValueError: chunk_size must be a positive number, not {chunkSize}")
  let mut parser ← IO.ofExcept (createFormParser headers config |>.mapError toString)
  let contentLength ← IO.ofExcept (contentLength? headers |>.mapError toString)
  let mut bytesRead := 0
  repeat
    let maxReadable := match contentLength with
      | some n => min (n - bytesRead) chunkSize
      | none => chunkSize
    let buff ← inputStream.read maxReadable.toUSize
    parser := parser.write buff
    bytesRead := bytesRead + buff.size
    if buff.size != maxReadable || contentLength == some bytesRead then break
  match ← parser.finalizeWith onField onFile with
  | .error e => throw (IO.userError (toString e))
  | .ok () => pure ()

end LeanMultipart
