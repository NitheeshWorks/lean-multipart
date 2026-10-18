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
  let (_, opts) := Options.parseB cd
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
  let (ctype, opts) := Options.parseB ct
  let boundary := (Options.lookup opts (ascii "boundary")).map (fun b => ByteArray.mk b.toArray)
  let kind ← FormKind.select (latin1Decode ⟨ctype.toArray⟩) boundary
  pure (FormParser.ofKind config kind fileName)

/-- Why Python's `int()` refuses a byte string. -/
inductive PyIntError where
  /-- "invalid literal for int() with base 10: …" -/
  | invalid
  /-- More than `pyIntMaxDigits` digits (Python's `sys.get_int_max_str_digits()`). -/
  | tooManyDigits (n : Nat)

/-- Python's default limit on the digits `int()` converts. -/
def pyIntMaxDigits : Nat := 4300

/-- Where `pyInt`'s scan is: before the number, after the sign, in the
digits, just after an underscore, after the number, or refused. -/
inductive PyIntPhase where
  | lead | sign | digits | underscore | trail | bad
  deriving DecidableEq

/-- `pyInt`'s scan state: the phase, the sign, the digits seen, and the
value of the digits while there are at most `pyIntMaxDigits` of them. -/
structure PyIntScan where
  phase : PyIntPhase := .lead
  neg : Bool := false
  count : Nat := 0
  value : Nat := 0

/-- One byte of Python's `int()` syntax. -/
def PyIntScan.step (s : PyIntScan) (c : UInt8) : PyIntScan :=
  let ws := c == 32 || (9 ≤ c && c ≤ 13)
  let digit := 48 ≤ c && c ≤ 57
  let addDigit (s : PyIntScan) : PyIntScan :=
    { s with phase := .digits, count := s.count + 1,
             value := if s.count < pyIntMaxDigits then s.value * 10 + (c - 48).toNat else s.value }
  match s.phase with
  | .lead => if ws then s else if c == 45 then { s with phase := .sign, neg := true }
    else if c == 43 then { s with phase := .sign } else if digit then addDigit s else { s with phase := .bad }
  | .sign | .underscore => if digit then addDigit s else { s with phase := .bad }
  | .digits => if digit then addDigit s else if c == 95 then { s with phase := .underscore }
    else if ws then { s with phase := .trail } else { s with phase := .bad }
  | .trail => if ws then s else { s with phase := .bad }
  | .bad => s

/-- Python's `int()` on a byte string: surrounding ASCII whitespace, an
optional sign, then decimal digits with single underscores between them,
at most 4300 digits (counted without sign and underscores, as Python counts
them). One pass over the packed bytes; digits past the limit are counted,
not converted, so a long value costs linear time and constant space. -/
def pyInt (b : ByteArray) : Except PyIntError Int :=
  let s := bytesFold PyIntScan.step b b.size 0 {}
  if s.phase != .digits && s.phase != .trail then .error .invalid
  else if pyIntMaxDigits < s.count then .error (.tooManyDigits s.count)
  else .ok (if s.neg then -(s.value : Int) else s.value)

/-- `Content-Length`, read as upstream's `parse_form` reads it. -/
def contentLength? (headers : Headers) : Except FormError (Option Nat) :=
  match headers.get "Content-Length" with
  | none => .ok none
  | some cl => match pyInt cl with
    | .error .invalid => .error (.badContentLength cl)
    | .error (.tooManyDigits n) => .error (.contentLengthDigits n)
    | .ok n => if n < 0 then .error .negativeContentLength else .ok (some n.toNat)

/-- Upstream's `parse_form(headers, input_stream, on_field, on_file)`, over
a body in memory: the fields and files, reading at most `Content-Length`
bytes if the header is present (see `parseFormStream` for a stream). -/
def parseForm (headers : Headers) (body : ByteArray) (config : FormParserConfig := {}) :
    Except FormError (List FormItem) := do
  let p ← createFormParser headers config
  let body ← match ← contentLength? headers with
    | none => pure body
    | some n => pure (body.extract 0 n)
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

/-! Starlette's form parsers enforce `max_fields`, `max_files` and
`max_part_size` from inside the parser callbacks, so a request is rejected
at the byte where it crosses a limit, before the rest is read. Here the
checks are byte machines wrapping the querystring and multipart machines:
the first excess stops the machine with the `LimitError` Starlette raises,
and from then on only the byte count moves. -/

/-- Starlette's view of a raw part: lower-cased header names, the last
`Content-Disposition`, its `name` and `filename`. -/
def partOf (p : RawPart) : Except LimitError StarlettePart := do
  let hs := p.headers.map (fun h => (lowerAscii h.1, h.2))
  let (name?, file?) := dispositionParams p.headers
  let some name := name? | .error .missingName
  pure { name := ⟨name.toArray⟩, filename := file?.map (fun f => ⟨f.toArray⟩), headers := hs, data := p.body }

/-! ### `application/x-www-form-urlencoded` -/

/-- The querystring machine and the first limit error. -/
structure UrlState where
  inner : QsState := {}
  err : Option LimitError := none
  deriving Inhabited

/-- One byte: step the querystring machine, then check the field being read
(`max_part_size` on its name and value) and the number of fields
(`max_fields`, checked when a field ends). -/
def urlStep (lim : FormLimits) (s : UrlState) (c : UInt8) : UrlState :=
  match s.err with
  | some _ => s
  | none =>
    let i' := Qs.step {} s.inner c
    if lim.maxPartSize < i'.name.size + i'.value.size then { inner := i', err := some (.fieldTooLarge lim.maxPartSize) }
    else if lim.maxFields < i'.fields.size then { inner := i', err := some (.tooManyFields lim.maxFields) }
    else { inner := i', err := none }

/-! A run of field data (see `Qs.valueSpan`) is taken at once here too,
cut short before the byte that would cross `max_part_size`. -/

/-- Where a run may end: before the byte that would cross `max_part_size`. -/
def urlStop (lim : FormLimits) (s : UrlState) (i stop : Nat) : Nat :=
  min stop (i + (lim.maxPartSize - (s.inner.name.size + s.inner.value.size)))

def urlSpan (lim : FormLimits) (s : UrlState) (b : ByteArray) (i stop : Nat) : Nat :=
  if s.err.isSome || lim.maxFields < s.inner.fields.size then 0
  else Qs.valueSpan s.inner b i (urlStop lim s i stop)

def urlBulk (s : UrlState) (b : ByteArray) (i n : Nat) : UrlState := { s with inner := Qs.valueBulk s.inner b i n }

theorem foldl_urlStep_value (lim : FormLimits) : ∀ (l : Bytes) (s : UrlState), s.err = none →
    s.inner.phase = .fieldData → (∀ x ∈ l, x ≠ Byte.AMP) → ¬ lim.maxFields < s.inner.fields.size →
    s.inner.name.size + s.inner.value.size + l.length ≤ lim.maxPartSize →
    l.foldl (urlStep lim) s = { s with inner := l.foldl (Qs.step {}) s.inner } := by
  intro l
  induction l with
  | nil => intro s _ _ _ _ _; rfl
  | cons c l ih =>
    intro s he hs hl hf hsz
    have hc := hl c (by simp)
    have hstep := Qs.step_value {} s.inner c hs hc
    have h1 : urlStep lim s c = { s with inner := Qs.step {} s.inner c } := by
      obtain ⟨inner, err⟩ := s
      simp only at he; subst he
      simp only at hs hf hsz hstep
      simp only [urlStep, hstep, ByteArray.size_push]
      simp at hsz
      have h2 : ¬ lim.maxPartSize < inner.name.size + (inner.value.size + 1) := by omega
      simp only [h2, hf, ↓reduceIte]
    rw [List.foldl_cons, List.foldl_cons, h1]
    refine ih _ he (by simp only [hstep]; exact hs) (fun x hx => hl x (by simp [hx])) (by simp only [hstep]; exact hf) ?_
    simp only [hstep, ByteArray.size_push]; simp at hsz; omega

theorem urlSpan_le (lim : FormLimits) (s : UrlState) (b : ByteArray) (i stop : Nat) :
    urlSpan lim s b i stop ≤ stop - i := by
  unfold urlSpan; split
  · exact Nat.zero_le _
  · have := Qs.valueSpan_le s.inner b i (urlStop lim s i stop)
    have : urlStop lim s i stop ≤ stop := by unfold urlStop; omega
    omega

theorem urlBulk_eq (lim : FormLimits) (s : UrlState) (b : ByteArray) (i stop : Nat) :
    urlBulk s b i (urlSpan lim s b i stop) = ((b.data.toList.drop i).take (urlSpan lim s b i stop)).foldl (urlStep lim) s := by
  have hle : urlSpan lim s b i stop ≤ Qs.valueSpan s.inner b i (urlStop lim s i stop) := by
    unfold urlSpan; split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  by_cases h0 : urlSpan lim s b i stop = 0
  · rw [h0]; simp [urlBulk, Qs.valueBulk]
  · have hc : ¬ (s.err.isSome || decide (lim.maxFields < s.inner.fields.size)) = true := by
      intro h; apply h0; unfold urlSpan; simp only [h, ↓reduceIte]
    have he : s.err = none := by
      cases h : s.err
      · rfl
      · simp [h] at hc
    have hf : ¬ lim.maxFields < s.inner.fields.size := by
      intro h; apply hc; simp [h]
    have hph := Qs.valueSpan_phase s.inner b i (urlStop lim s i stop) (by omega)
    unfold urlBulk
    rw [Qs.valueBulk_le {} s.inner b i _ _ hle]
    refine (foldl_urlStep_value lim _ s he hph
      (fun x hx => Qs.valueSpan_ne s.inner b i _ x (List.take_subset_take_left _ hle hx)) hf ?_).symm
    have hlen : ((b.data.toList.drop i).take (urlSpan lim s b i stop)).length ≤ urlSpan lim s b i stop :=
      List.length_take_le _ _
    have hd := Qs.valueSpan_le s.inner b i (urlStop lim s i stop)
    unfold urlStop at hd hle
    omega

def urlMachine (lim : FormLimits) : Machine UrlState :=
  { step := urlStep lim, pos := (·.inner.pos), limit := none,
    span := urlSpan lim, bulk := urlBulk, span_le := urlSpan_le lim, bulk_eq := urlBulk_eq lim }

/-- After a limit error nothing more is read. -/
def urlHalted (s : UrlState) : Bool := s.err.isSome

/-- The end of the body: a field in progress ends (and is counted). -/
def urlResult (lim : FormLimits) (s : UrlState) : Except LimitError (List QsField) :=
  match s.err with
  | some e => .error e
  | none =>
    let f := Qs.finish s.inner
    if lim.maxFields < f.fields.size then .error (.tooManyFields lim.maxFields) else .ok f.fields.toList

/-- Starlette's `FormParser`, streaming: `write` each chunk as it arrives,
then `finalize`. `error?` reports a limit as soon as it is crossed. -/
structure UrlencodedParser where
  lim : FormLimits := {}
  st : UrlState := {}
  deriving Inhabited

namespace UrlencodedParser
def write (p : UrlencodedParser) (chunk : ByteArray) : UrlencodedParser :=
  { p with st := (urlMachine p.lim).feedAUntil urlHalted p.st chunk }
def finalize (p : UrlencodedParser) : Except LimitError (List QsField) := urlResult p.lim p.st
def error? (p : UrlencodedParser) : Option LimitError := p.st.err
end UrlencodedParser

/-- Starlette's `FormParser.parse` over a whole body: the raw (still
percent-encoded) fields, in order, under the limits. -/
def parseUrlencodedRaw (lim : FormLimits) (body : ByteArray) : Except LimitError (List QsField) :=
  ((({ lim } : UrlencodedParser)).write body).finalize

/-! ### `multipart/form-data` -/

/-- The multipart machine, the counts of files and fields whose headers are
complete, whether the current part is a file, and the first limit error. -/
structure MpState where
  inner : MState := {}
  nFiles : Nat := 0
  nFields : Nat := 0
  curIsFile : Bool := false
  err : Option LimitError := none
  deriving Inhabited

/-- After a limit error, a parse error or the closing delimiter nothing more
is read (the rest is the epilogue, which is ignored). -/
def mpHalted (s : MpState) : Bool :=
  s.err.isSome || (match s.inner.phase with | .failed _ | .done => true | _ => false)

/-- One byte: step the multipart machine; when a part's headers end, check
its name and count it as a file or a field (`max_files`, `max_fields`); while
a field's data arrives, check its size (`max_part_size`). -/
def mpStep (cx : Mp.Ctx) (lim : FormLimits) (s : MpState) (c : UInt8) : MpState :=
  if mpHalted s then s else
  match s.err with
  | some _ => s
  | none =>
    let i' := Mp.step cx s.inner c
    match s.inner.phase, i'.phase with
    | .headersAlmostDone, .partData _ =>
      match dispositionParams i'.headers.toList with
      | (none, _) => { s with inner := i', err := some .missingName }
      | (some _, some _) =>
        if lim.maxFiles < s.nFiles + 1 then { s with inner := i', err := some (.tooManyFiles lim.maxFiles) }
        else { s with inner := i', nFiles := s.nFiles + 1, curIsFile := true }
      | (some _, none) =>
        if lim.maxFields < s.nFields + 1 then { s with inner := i', err := some (.tooManyFields lim.maxFields) }
        else { s with inner := i', nFields := s.nFields + 1, curIsFile := false }
    | .partData _, .partData _ =>
      if !s.curIsFile && lim.maxPartSize < i'.data.size then
        { s with inner := i', err := some (.partTooLarge lim.maxPartSize) }
      else { s with inner := i' }
    | _, _ => { s with inner := i' }

/-! A run of part data (see `Mp.dataSpan`) is taken at once here too, cut
short for a field part so that the byte crossing `max_part_size` is stepped
on its own. -/

/-- Where a run may end: for a field part, before the byte that would cross `max_part_size`. -/
def mpStop (lim : FormLimits) (s : MpState) (i stop : Nat) : Nat :=
  if s.curIsFile then stop else min stop (i + (lim.maxPartSize - s.inner.data.size))

def mpSpan (lim : FormLimits) (s : MpState) (b : ByteArray) (i stop : Nat) : Nat :=
  if s.err.isSome then 0 else Mp.dataSpan s.inner b i (mpStop lim s i stop)

def mpBulk (s : MpState) (b : ByteArray) (i n : Nat) : MpState := { s with inner := Mp.dataBulk s.inner b i n }

theorem mpStep_data (cx : Mp.Ctx) (lim : FormLimits) (s : MpState) (c : UInt8) (he : s.err = none)
    (hs : s.inner.phase = .partData (.idx 0)) (hc : c ≠ Byte.CR)
    (hsz : s.curIsFile = false → s.inner.data.size + 1 ≤ lim.maxPartSize) :
    mpStep cx lim s c = { s with inner := Mp.step cx s.inner c } := by
  have hstep := Mp.step_data cx s.inner c hs hc
  unfold mpStep
  simp only [mpHalted, he, hs, Option.isSome_none, Bool.false_or, hstep]
  cases hf : s.curIsFile
  · have := hsz hf; simp [ByteArray.size_push]; omega
  · simp

theorem foldl_mpStep_data (cx : Mp.Ctx) (lim : FormLimits) : ∀ (l : Bytes) (s : MpState), s.err = none →
    s.inner.phase = .partData (.idx 0) → (∀ x ∈ l, x ≠ Byte.CR) →
    (s.curIsFile = false → s.inner.data.size + l.length ≤ lim.maxPartSize) →
    l.foldl (mpStep cx lim) s = { s with inner := l.foldl (Mp.step cx) s.inner } := by
  intro l
  induction l with
  | nil => intro s _ _ _ _; rfl
  | cons c l ih =>
    intro s he hs hl hsz
    have hc := hl c (by simp)
    have hstep := Mp.step_data cx s.inner c hs hc
    rw [List.foldl_cons, List.foldl_cons, mpStep_data cx lim s c he hs hc
      (fun h => by have := hsz h; simp at this; omega)]
    refine ih _ he (by simp only [hstep]; exact hs) (fun x hx => hl x (by simp [hx])) ?_
    intro h; have := hsz h; simp only [hstep, ByteArray.size_push]; simp at this; omega

theorem mpSpan_le (lim : FormLimits) (s : MpState) (b : ByteArray) (i stop : Nat) :
    mpSpan lim s b i stop ≤ stop - i := by
  unfold mpSpan; split
  · exact Nat.zero_le _
  · have := Mp.dataSpan_le s.inner b i (mpStop lim s i stop)
    have : mpStop lim s i stop ≤ stop := by unfold mpStop; split <;> omega
    omega

theorem mpBulk_eq (cx : Mp.Ctx) (lim : FormLimits) (s : MpState) (b : ByteArray) (i stop : Nat) :
    mpBulk s b i (mpSpan lim s b i stop) = ((b.data.toList.drop i).take (mpSpan lim s b i stop)).foldl (mpStep cx lim) s := by
  have hle : mpSpan lim s b i stop ≤ Mp.dataSpan s.inner b i (mpStop lim s i stop) := by
    unfold mpSpan; split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  by_cases h0 : mpSpan lim s b i stop = 0
  · rw [h0]; simp [mpBulk, Mp.dataBulk]
  · have he : s.err = none := by
      unfold mpSpan at h0; cases h : s.err
      · rfl
      · simp [h] at h0
    have hph := Mp.dataSpan_phase s.inner b i (mpStop lim s i stop) (by omega)
    unfold mpBulk
    rw [Mp.dataBulk_le cx s.inner b i _ _ hle]
    refine (foldl_mpStep_data cx lim _ s he hph
      (fun x hx => Mp.dataSpan_ne s.inner b i _ x (List.take_subset_take_left _ hle hx)) ?_).symm
    intro hf
    have hlen : ((b.data.toList.drop i).take (mpSpan lim s b i stop)).length ≤ mpSpan lim s b i stop :=
      List.length_take_le _ _
    have hd := Mp.dataSpan_le s.inner b i (mpStop lim s i stop)
    simp only [mpStop, hf, Bool.false_eq_true, ↓reduceIte] at hd hle
    omega

def mpMachine (cx : Mp.Ctx) (lim : FormLimits) : Machine MpState :=
  { step := mpStep cx lim, pos := (·.inner.pos), limit := none,
    span := mpSpan lim, bulk := mpBulk, span_le := mpSpan_le lim, bulk_eq := mpBulk_eq cx lim }

/-- The parts read, or the first error (a parser error is Starlette's
"Invalid multipart data."). -/
def mpResult (s : MpState) : Except LimitError (List StarlettePart) :=
  match s.err with
  | some e => .error e
  | none =>
    match s.inner.phase with
    | .failed _ => .error .invalidMultipart
    | _ => s.inner.parts.toList.mapM partOf

/-- Starlette's `MultiPartParser`, streaming. -/
structure MultipartFormParser where
  cx : Mp.Ctx
  lim : FormLimits := {}
  st : MpState := {}

namespace MultipartFormParser
def new (boundary : Boundary) (lim : FormLimits := {}) : MultipartFormParser := { cx := { boundary }, lim }
def write (p : MultipartFormParser) (chunk : ByteArray) : MultipartFormParser :=
  { p with st := (mpMachine p.cx p.lim).feedAUntil mpHalted p.st chunk }
def finalize (p : MultipartFormParser) : Except LimitError (List StarlettePart) := mpResult p.st
def error? (p : MultipartFormParser) : Option LimitError := p.st.err
end MultipartFormParser

/-- The boundary parameter of a `Content-Type` value, if present. -/
def boundaryParam (contentType : ByteArray) : Option Bytes :=
  Options.lookup (Options.parseB contentType).2 (ascii "boundary")

/-- Starlette's `MultiPartParser.parse` over a whole body, under the limits. -/
def parseMultipartRaw (lim : FormLimits) (contentType body : ByteArray) :
    Except LimitError (List StarlettePart) :=
  match boundaryParam contentType with
  | none => .error .missingBoundary
  | some b =>
    match Boundary.ofBytes? ⟨b.toArray⟩ with
    | none => .error .invalidMultipart
    | some bd => ((MultipartFormParser.new bd lim).write body).finalize

end Starlette

end LeanMultipart
