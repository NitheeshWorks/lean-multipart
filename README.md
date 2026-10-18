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

Upstream's quickstart (`docs/index.md`), ported block by block in
[`examples/docs/Index.lean`](examples/docs/Index.lean); the index of ported
examples is [`examples/README.md`](examples/README.md). CI builds them and
checks their output against python-multipart's.

### Simple example

```python
import python_multipart

def simple_app(environ, start_response):
    ret = []

    # The following two callbacks just append the name to the return value.
    def on_field(field):
        ret.append(b"Parsed value parameter named: %s" % (field.field_name,))

    def on_file(file):
        ret.append(b"Parsed file parameter named: %s" % (file.field_name,))

    # Create headers object.
    headers = {'Content-Type': environ['CONTENT_TYPE']}
    if 'CONTENT_LENGTH' in environ:
        headers['Content-Length'] = environ['CONTENT_LENGTH']

    # Parse the form.
    python_multipart.parse_form(headers, environ['wsgi.input'], on_field, on_file)
    ...
```

```lean
import LeanMultipart
open LeanMultipart Wsgiref

def simpleApp (environ : Environ) (startResponse : StartResponse) : IO (List ByteArray) := do
  let ret ← IO.mkRef (#[] : Array ByteArray)

  -- The following two callbacks just append the name to the return value.
  let onField (field : Field) :=
    ret.modify (·.push ("Parsed value parameter named: ".toUTF8 ++ field.fieldName))

  let onFile (file : File) :=
    ret.modify (·.push ("Parsed file parameter named: ".toUTF8 ++ file.fieldName.getD .empty))

  -- Create headers object.
  let mut headers : Headers := [("Content-Type", environ["CONTENT_TYPE"]!)]
  if environ.contains "CONTENT_LENGTH" then
    headers := headers ++ [("Content-Length", environ["CONTENT_LENGTH"]!)]

  -- Parse the form.
  parseFormStream headers environ.wsgiInput onField onFile
  ...
```

### In-depth example: hashing each part as it streams

```python
content_type, params = parse_options_header(environ['CONTENT_TYPE'])
boundary = params.get(b'boundary')
callbacks = {'on_part_begin': on_part_begin, 'on_part_data': on_part_data, 'on_part_end': on_part_end}
parser = python_multipart.MultipartParser(boundary, callbacks)
inp = environ['wsgi.input']
size = int(environ['CONTENT_LENGTH'])
while size > 0:
    to_read = min(size, 1024 * 1024)
    data = inp.read(to_read)
    parser.write(data)
    size -= len(data)
    if len(data) != to_read:
        break
```

```lean
  let (_contentType, params) := parseOptionsHeader environ["CONTENT_TYPE"]!
  let boundary := params.get "boundary"
  let callbacks : MultipartCallbacks IO := { onPartBegin, onPartData, onPartEnd }
  let parser ← MultipartParser.create boundary callbacks
  let inp := environ.wsgiInput
  let mut size := int environ["CONTENT_LENGTH"]!
  while size > 0 do
    let toRead := min size (1024 * 1024)
    let data ← inp.read toRead.toUSize
    discard <| parser.write data
    size := size - data.size
    if data.size != toRead then
      break
```

`Environ`, `makeServer` and `Hashlib.sha256` are the examples' stand-ins for
Python's `wsgiref` and `hashlib` (`examples/support/`). The `IO` objects
(`MultipartParser.create`, `parseFormStream`) raise as upstream does; under
them are pure parsers (`MultipartParser.new`, `.write`, `parseForm`) whose
theorems are below.

## The public surface

| python-multipart | lean-multipart |
|---|---|
| `QuerystringParser(callbacks, strict_parsing, max_size)` | `QuerystringParser.new (strictParsing := …) (maxSize := …)`, `.write`, `.finalize`, `.writeWith`, `QuerystringCallbacks` |
| `MultipartParser(boundary, callbacks, max_size, max_header_count, max_header_size)` | `MultipartParser.create boundary callbacks cfg` (an `IO` object: `.write` raises), or pure: `MultipartParser.new boundary cfg`, `.write`, `.writeWith`, `MultipartCallbacks` |
| `OctetStreamParser(callbacks, max_size)` | `OctetStreamParser.new`, `.write`, `.finalize`, `OctetStreamCallbacks` |
| `FormParser(content_type, on_field, on_file, boundary=, file_name=, config=)` | `FormParser.create contentType boundary fileName config`, `.write`, `.finalize`, `.finalizeWith onField onFile` |
| `create_form_parser(headers, …)`, `parse_form(headers, stream, on_field, on_file)` | `createFormParser headers`, `parseFormStream headers stream onField onFile` (in `IO`), `parseForm headers body`, `parseFormWith` |
| `parse_options_header(value)` | `parseOptionsHeader value : ByteArray × Params`, `Params.get "boundary"` |
| `Field`, `File` (`field_name`, `value`, `file_name`, `content_type`, `size`) | `Field`, `File` (`fieldName`, `value`, `fileName`, `contentType`, `size`) |
| `Base64Decoder`, `QuotedPrintableDecoder` | the same names, `.write`, `.finalize` |
| `QuerystringParseError`, `MultipartParseError` (with `offset`) | the same names; `offset` is chunk-relative, `error.offset` absolute |
| Starlette's `FormParser` / `MultiPartParser` with `max_fields`, `max_files`, `max_part_size` | streaming: `Starlette.UrlencodedParser`, `Starlette.MultipartFormParser` (`.write chunk`, `.error?`, `.finalize`); whole body: `API.Starlette.parseUrlencoded`, `API.Starlette.parseMultipartForm` |

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
| Starlette's limits, enforced as bytes arrive | an accepted form has at most `max_fields` fields, `max_files` files, every field within `max_part_size` (`parseUrlencodedRaw_ok`, `parseMultipartRaw_ok`); and while no limit error has been raised the parser's state is within the limits (`urlencoded_bounded`, `multipart_bounded`): it stops at the byte that crosses one, so no state beyond the limit is kept; any chunking gives the result of one write (`finalize_chunks`) |

The round trips are instances of one codec theory (`Theory/Codec.lean`): a
judgement `Reads M P w Q` for byte machines and one lemma per printer
combinator (`append`, `flatMap`, `sepBy`). The chunking theorems rest on
`Theory/Machine.lean`, proved once for every byte machine.

What is tested rather than proved, and every deviation from upstream, is in
[CONTRIBUTING.md](CONTRIBUTING.md#verification) and `docs/traceability.toml`.

## Performance

`scripts/bench.sh` (run in CI) builds each body natively and checks time and
peak memory against the bounds in `tests/Bench.lean`; the peak includes the
body itself. Starlette takes 73 to 109 ms and about 121 MB when a limit stops
a 50 MB body, and 455 ms to parse a whole 50 MB file part.

| Input | Outcome | Parse time | Peak memory |
|---|---|---|---|
| `a=` + 50 MB value | `fieldTooLarge` | 64 ms | 68 MB |
| one 50 MB multipart field | `partTooLarge` | 3 ms | 64 MB |
| 1,000,000 tiny parts (58 MB) | `tooManyFields` | 9 ms | 68 MB |
| 1,000,000 `a=b&` (4 MB) | `tooManyFields` | < 1 ms | 13 MB |
| 50 MB file part, whole body | parsed | 150 ms | 115 MB |
| 50 MB random binary file part, whole body | parsed | 260 ms | 220 MB |
| 50 MB file part, `MultipartParser` in 64 KB chunks | streamed | 150 ms | 68 MB |

Parsers read the packed bytes directly and keep their buffers in
`ByteArray`; the limit parsers stop reading at the first error. Inside part
data the multipart machine finds the next `CR` and appends the run before it
with one copy (`Mp.dataSpan`, `Mp.dataBulk`); `Mp.dataBulk_eq` proves that is
what stepping byte by byte does, so every theorem is about the byte-wise
`step`.

## Building and testing

```
lake build              # library, proofs, tests, examples
lake exe props          # 15 seeded properties (`lake exe props 42`)
scripts/bench.sh        # native time and memory checks on 50 MB bodies
lake exe conformance    # cases re-expressed from python-multipart's and Starlette's tests
lake exe docs-index     # the ported docs/index.md examples (see examples/README.md)
scripts/check.sh --pbt  # the whole CI gate
```

Toolchain: `leanprover/lean4:v4.35.0` (`lean-toolchain`).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution (python-multipart,
Apache-2.0) is in [NOTICE](NOTICE).
