# lean-multipart

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [python-multipart](https://github.com/Kludex/python-multipart),
the streaming form parser Starlette uses, to Lean 4: `multipart/form-data`,
`application/x-www-form-urlencoded` and `application/octet-stream`, with the
same parsers (`QuerystringParser`, `MultipartParser`, `OctetStreamParser`,
`FormParser`), the same helpers (`parse_options_header`, `create_form_parser`,
`parse_form`) and the same limits, and with machine-checked proofs that the
parsers read back what the printers write and that streaming gives the
whole-buffer result for every split of the input.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo. This one depends on Lean
core only; lean-starlette depends on it.

## Quickstart

Upstream's quickstart (`docs/index.md`), translated. The code below is
`examples/Quickstart.lean`, built and run in CI (`lake exe quickstart`).

### Simple example

```python
import python_multipart

def simple_app(environ, start_response):
    ret = []
    def on_field(field):
        ret.append(b"Parsed value parameter named: %s" % (field.field_name,))
    def on_file(file):
        ret.append(b"Parsed file parameter named: %s" % (file.field_name,))
    headers = {'Content-Type': environ['CONTENT_TYPE']}
    python_multipart.parse_form(headers, environ['wsgi.input'], on_field, on_file)
    ...
```

```lean
import LeanMultipart
open LeanMultipart

def simpleApp (contentType body : ByteArray) : Except FormError (List String) := do
  let items ← parseForm [("Content-Type", contentType)] body
  return items.map fun
    | .field f => s!"Parsed value parameter named: {latin1Decode f.fieldName}"
    | .file f => s!"Parsed file parameter named: {(f.fieldName.map latin1Decode).getD ""}"
```

Or with callbacks, in any monad, as upstream's `on_field` / `on_file`:

```lean
def simpleAppWith (contentType body : ByteArray) : StateM (Array String) (Except FormError Unit) :=
  parseFormWith [("Content-Type", contentType)] body
    (onField := fun f => modify (·.push s!"Parsed value parameter named: {latin1Decode f.fieldName}"))
    (onFile := fun f => modify (·.push s!"Parsed file parameter named: {(f.fieldName.map latin1Decode).getD ""}"))
```

### In-depth example: streaming the parts

```python
from python_multipart.multipart import parse_options_header

content_type, params = parse_options_header(environ['CONTENT_TYPE'])
boundary = params.get(b'boundary')
callbacks = {'on_part_begin': on_part_begin, 'on_part_data': on_part_data, 'on_part_end': on_part_end}
parser = python_multipart.MultipartParser(boundary, callbacks)
while chunk := environ['wsgi.input'].read(1024 * 1024):
    parser.write(chunk)
```

```lean
def partChecksums (contentType : ByteArray) (chunks : List ByteArray) : Except String (List Nat) := do
  let (_, params) := parseOptionsHeader contentType
  let some b := params.get "boundary" | throw "no boundary"
  let some boundary := Boundary.ofBytes? b | throw "invalid boundary"
  let mut parser := MultipartParser.new boundary
  let mut sums : Array Nat := #[]
  let mut current := 0
  for chunk in chunks do
    match parser.write chunk with
    | .error e => throw s!"parse error at offset {e.offset}"
    | .ok (p, events, _) =>
      parser := p
      for ev in events do
        match ev with
        | .partBegin => current := 0
        | .partData d => current := d.foldl (fun acc x => acc + x.toNat) current
        | .partEnd => sums := sums.push current
        | _ => pure ()
  return sums.toList
```

(Upstream hashes each part with SHA-256; this library has no hash, so the
example sums the bytes.) `parser.writeWith callbacks chunk` fires a
`MultipartCallbacks` record instead (`onPartBegin`, `onPartData`, ...), and
`QuerystringParser` / `OctetStreamParser` work the same way.

## The public surface

| python-multipart | lean-multipart |
|---|---|
| `QuerystringParser(callbacks, strict_parsing, max_size)` | `QuerystringParser.new (strictParsing := …) (maxSize := …)`, `.write`, `.finalize`, `.writeWith`, `QuerystringCallbacks` |
| `MultipartParser(boundary, callbacks, max_size, max_header_count, max_header_size)` | `MultipartParser.new boundary cfg`, `.write`, `.writeWith`, `MultipartCallbacks` |
| `OctetStreamParser(callbacks, max_size)` | `OctetStreamParser.new`, `.write`, `.finalize`, `OctetStreamCallbacks` |
| `FormParser(content_type, on_field, on_file, boundary=, file_name=, config=)` | `FormParser.create contentType boundary fileName config`, `.write`, `.finalize`, `.finalizeWith onField onFile` |
| `create_form_parser(headers, …)`, `parse_form(headers, stream, on_field, on_file)` | `createFormParser headers`, `parseForm headers body`, `parseFormWith` |
| `parse_options_header(value)` | `parseOptionsHeader value : ByteArray × Params`, `Params.get "boundary"` |
| `Field`, `File` (`field_name`, `value`, `file_name`, `content_type`, `size`) | `Field`, `File` (`fieldName`, `value`, `fileName`, `contentType`, `size`) |
| `Base64Decoder`, `QuotedPrintableDecoder` | the same names, `.write`, `.finalize` |
| `QuerystringParseError`, `MultipartParseError` (with `offset`) | the same names; `offset` is chunk-relative, `error.offset` absolute |
| Starlette's `FormParser` / `MultiPartParser` limits | `API.Starlette.parseUrlencoded`, `API.Starlette.parseMultipartForm` (`max_fields`, `max_files`, `max_part_size`) |

Functions with a refinement in their type, in `LeanMultipart.API`
(`LeanMultipart/APIs/`), are what lean-starlette imports:

* `API.parseBoundary contentType : Except BoundaryError {b // ValidBoundary b}`
* `API.parseMultipart boundary cfg body : {r // Spec.MpParseSpec … body r}` (every
  chunking agrees, the error offset is inside the body)
* `API.printMultipart cx parts hw hf : {body // ∀ epi, (Mp.parse cx (body ++ epi)).toExcept = .ok parts}`,
  and `API.printMultipart?` checking its precondition at runtime
* `API.urlencode ps : {body // urldecodeB body = ps}`, `API.urldecode`,
  `API.percentEncode`, `API.quotePlus`, `API.parseQuerystring`
* `API.parseForm`, `API.Starlette.parseUrlencoded lim body : Except LimitError {fs // fs.length ≤ lim.maxFields ∧ …}`,
  `API.Starlette.parseMultipartForm lim contentType body : Except LimitError {ps // … ≤ lim.maxFiles ∧ …}`

## What is proved

Every theorem below is bundled in `LeanMultipart/Proofs/Verified.lean`; CI
checks that it reaches only Lean's three axioms.

| Property | Lean statement |
|---|---|
| Percent-encoding round trip, any continuation | `percentDecode (percentEncode b ++ rest) = b ++ percentDecode rest` |
| `quote_plus` round trip | `unquotePlus (quotePlus b ++ rest) = b ++ unquotePlus rest` |
| Urlencoded round trip | `urldecodeB (urlencodeB ps) = ps`, and `urldecodeB (urlencodeB ps ++ "&" ++ rest) = ps ++ urldecodeB rest` |
| Multipart round trip, any epilogue | `(Mp.parse cx (Mp.print cx.boundary ps ++ epi)).toExcept = .ok ps`, for well-formed parts (no body contains `CR LF --boundary`; header names are tokens; values have no `CR` and no leading space; within the header limits) |
| Content-Disposition round trip | `dispositionParams (formPart n f ct body).headers = (some n, f)`, for names without `"`, `\` or `;` |
| Streaming equals whole-buffer, every split | `QuerystringParser.parseChunks cfg chunks = Qs.parse cfg (concatChunks chunks)`; `MultipartParser.parseChunks cx chunks = (Mp.parse cx (concatChunks chunks)).toExcept`; `(chunks.foldl FormParser.write p) = p.write (concatChunks chunks)` |
| Totality | the parsers process `min(len, max_size)` bytes and report errors at offsets inside them (`Qs.parse_total`, `Mp.parse_total`) |
| A parsed boundary is valid | `API.parseBoundary` returns `{b // ValidBoundary b}` |
| Starlette's limits | an accepted form has at most `max_fields` fields, `max_files` files, every field within `max_part_size` |

The round trips are instances of one codec theory (`Theory/Codec.lean`): a
judgement `Reads M P w Q` for byte machines and one lemma per printer
combinator (`append`, `flatMap`, `sepBy`). The chunking theorems rest on
`Theory/Machine.lean`, proved once for every byte machine.

What is tested rather than proved, and every deviation from upstream, is in
[CONTRIBUTING.md](CONTRIBUTING.md#verification) and `docs/traceability.toml`.

## Building and testing

```
lake build              # library, proofs, tests, quickstart
lake exe props          # 14 seeded properties (`lake exe props 42`)
lake exe conformance    # cases re-expressed from python-multipart's and Starlette's tests
lake exe quickstart     # the examples above
scripts/check.sh --pbt  # the whole CI gate
```

Toolchain: `leanprover/lean4:v4.35.0` (`lean-toolchain`).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution (python-multipart,
Apache-2.0) is in [NOTICE](NOTICE).
