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
  toString e := s!"MultipartParseError: {e.error.kind.message} (offset {e.offset})"

instance : ToString FormError where
  toString
    | .multipart e => s!"MultipartParseError: {e.kind.message} (offset {e.offset})"
    | .querystring e => s!"QuerystringParseError: {match e.kind with
        | .duplicateAmpersand => "Skipping duplicate ampersand"
        | .missingEquals => "When strict_parsing is True, we require an equals sign in all field chunks"} (offset {e.offset})"
    | .noBoundary => "FormParserError: No boundary given"
    | .badBoundary => "FormParserError: Invalid boundary"
    | .unknownContentType ct => s!"FormParserError: Unknown Content-Type: {ct}"
    | .noContentType => "ValueError: No Content-Type header given!"
    | .badContentLength => "ValueError: Content-Length must be a non-negative integer"
    | .missingFieldName => "FormParserError: Field name not found in Content-Disposition"
    | .badCte _ => "FormParserError: Unknown Content-Transfer-Encoding"
    | .decode _ => "DecodeError: invalid base64 data"

/-- A `MultipartParser` with its callbacks, as upstream's mutable object. -/
structure MultipartParser.Object where
  parser : IO.Ref MultipartParser
  callbacks : MultipartCallbacks IO

/-- Upstream's `MultipartParser(boundary, callbacks)`. The boundary is the
`params.get(b"boundary")` of `parse_options_header`; a missing or invalid
one raises, as upstream's constructor does. -/
def MultipartParser.create (boundary : Option ByteArray) (callbacks : MultipartCallbacks IO := {})
    (config : MultipartConfig := {}) : IO MultipartParser.Object := do
  let some b := boundary | throw (IO.userError "FormParserError: No boundary given")
  let some bd := Boundary.ofBytes? b | throw (IO.userError "FormParserError: Invalid boundary")
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
`Content-Length`, write each to the parser, then call `onField` / `onFile`
for each field and file in order. Errors are raised as `IO` errors. -/
def parseFormStream (headers : Headers) (inputStream : IO.FS.Stream) (onField : Field → IO Unit)
    (onFile : File → IO Unit) (chunkSize : Nat := 1048576) (config : FormParserConfig := {}) : IO Unit := do
  if chunkSize < 1 then throw (IO.userError s!"ValueError: chunk_size must be a positive number, not {chunkSize}")
  let mut parser ← IO.ofExcept (createFormParser headers config |>.mapError toString)
  let contentLength ← match headers.get "Content-Length" with
    | none => pure none
    | some cl => match (latin1Decode cl).trimAscii.toString.toNat? with
      | some n => pure (some n)
      | none => throw (IO.userError (toString FormError.badContentLength))
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
