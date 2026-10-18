import LeanMultipart.DataTypes.Form
import LeanMultipart.RepoImpl.Querystring
import LeanMultipart.RepoImpl.Multipart
import LeanMultipart.RepoImpl.Options
import LeanMultipart.RepoImpl.Decoders

/-!
# The form layer

Upstream's `FormParser`: it picks the parser from the `Content-Type`, and
turns the parser's output into `Field` and `File` values. And the two
Starlette form parsers, which drive `QuerystringParser` and
`MultipartParser` directly and enforce `max_fields`, `max_files` and
`max_part_size`.

Every function here is a pure function of the state machine's final state,
so the chunking theorems of the machines carry over unchanged.

Order of errors: upstream raises from inside callbacks, in stream order.
A parser error can only occur in a boundary or header line, so it comes
after every completed part and after the headers of the part in progress;
the functions below check completed parts in order, then the part in
progress, then the parser error, which is the same order.
-/

namespace LeanMultipart

/-- Look a header up by lower-cased name; the last occurrence wins, as in
upstream's `headers` dict. -/
def headerLookup (hs : List (ByteArray × ByteArray)) (name : Bytes) : Option ByteArray :=
  (hs.reverse.find? (fun h => (lowerAscii h.1).data.toList == name)).map (·.2)

/-- The `name` and `filename` parameters of a part's `Content-Disposition`. -/
def dispositionParams (hs : List (ByteArray × ByteArray)) : Option Bytes × Option Bytes :=
  let cd := (headerLookup hs (ascii "content-disposition")).getD ByteArray.empty
  let (_, opts) := Options.parseL cd.data.toList
  (Options.lookup opts (ascii "name"), Options.lookup opts (ascii "filename"))

def toDecodeKind : DecodeError → DecodeErrorKind
  | .base64Padding => .base64Padding
  | .base64Leftover _ => .base64Leftover

namespace Form

/-- How a part's body is decoded. -/
inductive Cte where
  | identity
  | base64
  | quotedPrintable

/-- `on_headers_finished`: the field name and filename, and the transfer
encoding. -/
def headersFinished (cfg : FormParserConfig) (hs : List (ByteArray × ByteArray)) :
    Except FormError (Bytes × Option Bytes × Cte) := do
  let (name?, file?) := dispositionParams hs
  let some name := name? | .error .missingFieldName
  let cte := lowerAscii ((headerLookup hs (ascii "content-transfer-encoding")).getD ⟨(ascii "7bit").toArray⟩)
  let l := cte.data.toList
  let enc ←
    if l == ascii "binary" || l == ascii "8bit" || l == ascii "7bit" then pure Cte.identity
    else if l == ascii "base64" then pure Cte.base64
    else if l == ascii "quoted-printable" then pure Cte.quotedPrintable
    else if cfg.errorOnBadCte then .error (.badCte cte)
    else pure Cte.identity
  pure (name, file?, enc)

/-- A completed part as upstream's `FormParser` reports it. -/
def item (cfg : FormParserConfig) (p : RawPart) : Except FormError FormItem := do
  let (name, file?, enc) ← headersFinished cfg p.headers
  let data ← match enc with
    | .identity => pure p.body
    | .base64 => (decodeBase64 p.body).mapError (FormError.decode ∘ toDecodeKind)
    | .quotedPrintable => pure (decodeQuotedPrintable p.body)
  let ct := headerLookup p.headers (ascii "content-type")
  match file? with
  | none => pure (.field { fieldName := ⟨name.toArray⟩, value := some data, contentType := ct })
  | some fn => pure (.file { fieldName := some ⟨name.toArray⟩, fileName := some ⟨fn.toArray⟩,
                             contentType := ct, headers := p.headers, data })

/-- The checks upstream makes on the part in progress when the input ends:
its headers, and the base64 data written so far. -/
def checkCurrent (cfg : FormParserConfig) (p : RawPart) : Except FormError Unit := do
  let (_, _, enc) ← headersFinished cfg p.headers
  match enc with
  | .base64 =>
    match ({} : Base64Decoder).write p.body with
    | .ok _ => pure ()
    | .error e => .error (.decode (toDecodeKind e))
  | _ => pure ()

def itemsOf (cfg : FormParserConfig) : List RawPart → Except FormError (List FormItem)
  | [] => .ok []
  | p :: ps => do
    let i ← item cfg p
    let is ← itemsOf cfg ps
    pure (i :: is)

/-- `FormParser` over a multipart result. -/
def ofMultipart (cfg : FormParserConfig) (r : MultipartResult) : Except FormError (List FormItem) := do
  let items ← itemsOf cfg r.parts
  if let some p := r.current then checkCurrent cfg p
  if let some e := r.error then .error (.multipart e)
  pure items

/-- `FormParser` over a querystring result. -/
def ofQs (r : Except QsError (List QsField)) : Except FormError (List FormItem) :=
  match r with
  | .error e => .error (.querystring e)
  | .ok fs => .ok (fs.map fun f =>
      .field { fieldName := f.1, value := if f.2.size == 0 then none else some f.2 })

def mpConfig (cfg : FormParserConfig) : MultipartConfig :=
  { maxSize := cfg.maxBodySize, maxHeaderCount := cfg.maxHeaderCount, maxHeaderSize := cfg.maxHeaderSize,
    h_maxSize := cfg.h_maxBodySize }

end Form

/-- Which parser a `Content-Type` selects. -/
inductive FormKind where
  | octetStream
  | urlencoded
  | multipart (b : Boundary)

/-- Upstream's `FormParser.__init__` dispatch. -/
def FormKind.select (contentType : String) (boundary : Option ByteArray) : Except FormError FormKind :=
  if contentType == "application/octet-stream" then .ok .octetStream
  else if contentType == "application/x-www-form-urlencoded" || contentType == "application/x-url-encoded" then
    .ok .urlencoded
  else if contentType == "multipart/form-data" then
    match boundary with
    | none => .error .noBoundary
    | some b => match Boundary.ofBytes? b with
      | some bd => .ok (.multipart bd)
      | none => .error .badBoundary
  else .error (.unknownContentType contentType)

/-- Upstream's `FormParser`, as a state machine fed chunks. -/
inductive FormParser where
  | octet (cfg : FormParserConfig) (fileName : Option ByteArray) (data : Array UInt8)
  | qs (cfg : FormParserConfig) (st : QsState)
  | mp (cfg : FormParserConfig) (cx : Mp.Ctx) (st : MState)

namespace FormParser

/-- A parser for an already-selected kind. -/
def ofKind (cfg : FormParserConfig) (kind : FormKind) (fileName : Option ByteArray := none) : FormParser :=
  match kind with
  | .octetStream => .octet cfg fileName #[]
  | .urlencoded => .qs cfg {}
  | .multipart b => .mp cfg { boundary := b, cfg := Form.mpConfig cfg } {}

/-- Feed a chunk. -/
def write (p : FormParser) (chunk : ByteArray) : FormParser :=
  match p with
  | .octet cfg fn data =>
    let room := match cfg.maxBodySize with
      | none => chunk.size
      | some m => min chunk.size (m - data.size)
    .octet cfg fn (data ++ chunk.data.extract 0 room)
  | .qs cfg st => .qs cfg (Qs.feedA { maxSize := cfg.maxBodySize, h_maxSize := cfg.h_maxBodySize } st chunk)
  | .mp cfg cx st => .mp cfg cx (Mp.feedA cx st chunk)

/-- Finish: every field and file, in order, or the first error. -/
def finalize (p : FormParser) : Except FormError (List FormItem) :=
  match p with
  | .octet _ fn data => .ok [.file { fieldName := none, fileName := fn, data := ⟨data⟩ }]
  | .qs _ st => Form.ofQs (Qs.result st)
  | .mp cfg _ st => Form.ofMultipart cfg (Mp.result st)

/-- The concatenation of chunks. -/
abbrev concat (cs : List ByteArray) : ByteArray := concatChunks cs

/-- Upstream's `FormParser(content_type, on_field, on_file, boundary=…,
file_name=…, config=…)`; the callbacks are given to `finalizeWith`. -/
def create (contentType : String) (boundary : Option ByteArray := none) (fileName : Option ByteArray := none)
    (config : FormParserConfig := {}) : Except FormError FormParser :=
  (FormKind.select contentType boundary).map (ofKind config · fileName)

/-- `finalize`, calling `onField` and `onFile` for each item in order. -/
def finalizeWith {m : Type → Type} [Monad m] (p : FormParser) (onField : Field → m Unit)
    (onFile : File → m Unit) : m (Except FormError Unit) := do
  match p.finalize with
  | .error e => pure (.error e)
  | .ok items =>
    for i in items do
      match i with
      | .field f => onField f
      | .file f => onFile f
    pure (.ok ())

end FormParser

/-- The whole-buffer form parser. -/
def parseFormBody (cfg : FormParserConfig) (kind : FormKind) (body : ByteArray)
    (fileName : Option ByteArray := none) : Except FormError (List FormItem) :=
  ((FormParser.ofKind cfg kind fileName).write body).finalize

/-- Request headers, as upstream's `headers` dict (keys are matched exactly,
as upstream's `dict.get` does). -/
abbrev Headers := List (String × ByteArray)

def Headers.get (h : Headers) (k : String) : Option ByteArray := (h.find? (·.1 == k)).map (·.2)

/-- Upstream's `create_form_parser(headers, …)`: read `Content-Type` and its
`boundary`. -/
def createFormParser (headers : Headers) (config : FormParserConfig := {})
    (fileName : Option ByteArray := none) : Except FormError FormParser := do
  let some ct := headers.get "Content-Type" | .error .noContentType
  let (ctype, opts) := Options.parseL ct.data.toList
  let boundary := (Options.lookup opts (ascii "boundary")).map (fun b => ByteArray.mk b.toArray)
  let kind ← FormKind.select (latin1Decode ⟨ctype.toArray⟩) boundary
  pure (FormParser.ofKind config kind fileName)

/-- Upstream's `parse_form(headers, input_stream, on_field, on_file)`: the
fields and files of a body, reading at most `Content-Length` bytes if the
header is present. -/
def parseForm (headers : Headers) (body : ByteArray) (config : FormParserConfig := {}) :
    Except FormError (List FormItem) := do
  let p ← createFormParser headers config
  let body ← match headers.get "Content-Length" with
    | none => pure body
    | some cl => match (latin1Decode cl).trimAscii.toString.toNat? with
      | some n => pure (body.extract 0 n)
      | none => .error .badContentLength
  (p.write body).finalize

/-- `parse_form` with upstream's `on_field` / `on_file` callbacks. -/
def parseFormWith {m : Type → Type} [Monad m] (headers : Headers) (body : ByteArray)
    (onField : Field → m Unit) (onFile : File → m Unit) (config : FormParserConfig := {}) :
    m (Except FormError Unit) := do
  match parseForm headers body config with
  | .error e => pure (.error e)
  | .ok items =>
    for i in items do
      match i with
      | .field f => onField f
      | .file f => onFile f
    pure (.ok ())

/-! ## Printing form parts -/

/-- `form-data; name="…"` and, for a file, `; filename="…"`. Names are
written inside double quotes without escaping, so the round trip through
`parse_options_header` needs names without `"`, `\`, `;`, `CR` or `LF`
(see UP-005 for what upstream does with a trailing backslash). -/
def dispositionValue (name : ByteArray) (filename : Option ByteArray) : ByteArray :=
  let q : ByteArray := ⟨#[Byte.DQUOTE]⟩
  let base := ⟨(ascii "form-data; name=").toArray⟩ ++ q ++ name ++ q
  match filename with
  | none => base
  | some f => base ++ ⟨(ascii "; filename=").toArray⟩ ++ q ++ f ++ q

/-- A form part with `Content-Disposition` and, if given, `Content-Type`. -/
def formPart (name : ByteArray) (filename : Option ByteArray) (contentType : Option ByteArray)
    (body : ByteArray) : RawPart :=
  { headers := (⟨(ascii "Content-Disposition").toArray⟩, dispositionValue name filename) ::
      (match contentType with
       | none => []
       | some ct => [(⟨(ascii "Content-Type").toArray⟩, ct)])
    body }

/-! ## Starlette's form parsers -/

namespace Starlette

/-- Starlette's `FormParser` over the raw fields, in order. -/
def checkFields (lim : FormLimits) : Nat → List QsField → Except LimitError (List QsField)
  | _, [] => .ok []
  | n, f :: fs =>
    if lim.maxPartSize < f.1.size + f.2.size then .error (.fieldTooLarge lim.maxPartSize)
    else if lim.maxFields < n + 1 then .error (.tooManyFields lim.maxFields)
    else (checkFields lim (n + 1) fs).map (f :: ·)

/-- Starlette's view of a raw part: lower-cased header names, the last
`Content-Disposition`, its `name` and `filename`. -/
def partOf (p : RawPart) : Except LimitError StarlettePart := do
  let hs := p.headers.map (fun h => (lowerAscii h.1, h.2))
  let (name?, file?) := dispositionParams p.headers
  let some name := name? | .error .missingName
  pure { name := ⟨name.toArray⟩, filename := file?.map (fun f => ⟨f.toArray⟩), headers := hs, data := p.body }

/-- Starlette's per-part checks, in order; `nf` / `nd` count files and
fields so far. `last` marks the part in progress, whose data is not
reported (only checked). -/
def checkPart (lim : FormLimits) (nf nd : Nat) (p : RawPart) :
    Except LimitError (StarlettePart × Nat × Nat) := do
  let sp ← partOf p
  if sp.isFile then
    if lim.maxFiles < nf + 1 then .error (.tooManyFiles lim.maxFiles)
    else pure (sp, nf + 1, nd)
  else
    if lim.maxFields < nd + 1 then .error (.tooManyFields lim.maxFields)
    else if lim.maxPartSize < p.body.size then .error (.partTooLarge lim.maxPartSize)
    else pure (sp, nf, nd + 1)

def checkParts (lim : FormLimits) : Nat → Nat → List RawPart → Except LimitError (List StarlettePart × Nat × Nat)
  | nf, nd, [] => .ok ([], nf, nd)
  | nf, nd, p :: ps => do
    let (sp, nf', nd') ← checkPart lim nf nd p
    let (sps, nf'', nd'') ← checkParts lim nf' nd' ps
    pure (sp :: sps, nf'', nd'')

/-- Starlette's `MultiPartParser` over a multipart result. -/
def ofMultipart (lim : FormLimits) (r : MultipartResult) : Except LimitError (List StarlettePart) := do
  let (sps, nf, nd) ← checkParts lim 0 0 r.parts
  if let some p := r.current then
    let _ ← checkPart lim nf nd p
  if r.error.isSome then .error .invalidMultipart
  pure sps

/-- Starlette's `FormParser.parse`: the raw (still percent-encoded) fields,
in order, under the limits. -/
def parseUrlencodedRaw (lim : FormLimits) (body : ByteArray) : Except LimitError (List QsField) :=
  match Qs.parse {} body with
  | .ok fs => checkFields lim 0 fs
  | .error _ => .error .invalidMultipart

/-- The boundary parameter of a `Content-Type` value, if present. -/
def boundaryParam (contentType : ByteArray) : Option Bytes :=
  Options.lookup (Options.parseL contentType.data.toList).2 (ascii "boundary")

/-- Starlette's `MultiPartParser.parse`, under the limits. -/
def parseMultipartRaw (lim : FormLimits) (contentType body : ByteArray) :
    Except LimitError (List StarlettePart) :=
  match boundaryParam contentType with
  | none => .error .missingBoundary
  | some b =>
    match Boundary.ofBytes? ⟨b.toArray⟩ with
    | none => .error .invalidMultipart
    | some bd => ofMultipart lim (Mp.parse { boundary := bd } body)

end Starlette

end LeanMultipart
