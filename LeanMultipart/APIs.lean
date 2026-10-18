import LeanMultipart.RepoImpl
import LeanMultipart.Proofs.Stream
import LeanMultipart.APIs.Codec
import LeanMultipart.APIs.Multipart
import LeanMultipart.APIs.Form

/-!
# The public surface

`import LeanMultipart` brings in everything below.

**Upstream's API** (namespace `LeanMultipart`), named as python-multipart:

* `QuerystringParser`, `MultipartParser`, `OctetStreamParser`: `.new`,
  `.write chunk` (events and bytes processed, or `QuerystringParseError` /
  `MultipartParseError`), `.finalize`, and `.writeWith callbacks chunk` with
  `QuerystringCallbacks` / `MultipartCallbacks` / `OctetStreamCallbacks` in
  any monad.
* `FormParser.create contentType boundary fileName config`, `.write`,
  `.finalize`, `.finalizeWith onField onFile`; `createFormParser headers`,
  `parseForm headers body`, `parseFormWith headers body onField onFile`;
  `Field`, `File`, `FormItem`, `FormError`.
* `parseOptionsHeader value : ByteArray × Params`, `Params.get key`.
* `Base64Decoder`, `QuotedPrintableDecoder`.
* `Starlette.UrlencodedParser`, `Starlette.MultipartFormParser`: Starlette's
  form parsers, streaming, with `max_fields` / `max_files` / `max_part_size`
  enforced as bytes arrive (`.write`, `.error?`, `.finalize`).
* `Boundary` (with `Boundary.ofBytes?`), `RawPart`, `Mp.parse`, `Mp.print`,
  `Qs.parse`, `percentEncode`, `percentDecode`, `quotePlus`, `unquotePlus`,
  `urlencodeB`, `urldecodeB`, `formPart`, `dispositionValue`.

**Refined API** (namespace `LeanMultipart.API`), each result carrying its
proved postcondition:

* `API.parseBoundary : ByteArray → Except BoundaryError {b // ValidBoundary b}`
* `API.parseMultipart`, `API.parseQuerystring`, `API.parseForm`: results that
  every chunking of the input reproduces, errors located inside the input
* `API.printMultipart`, `API.printMultipart?`: bodies that parse back to the
  given parts on any epilogue
* `API.urlencode`, `API.percentEncode`, `API.quotePlus`: encodings with
  their decoding round trip
* `API.Starlette.parseUrlencoded`, `API.Starlette.parseMultipartForm`:
  Starlette's form parsing with `max_fields`, `max_files`, `max_part_size`,
  returning forms that satisfy the limits

The theorems behind these are listed in `Proofs/Verified.lean` and in the
README's "What is proved".
-/
