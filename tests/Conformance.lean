import LeanMultipart
import tests.Fixtures

/-!
# Conformance cases

Each case re-expresses one upstream test (python-multipart `tests/`, and
Starlette `tests/test_formparsers.py` for the limits) in Lean and names it,
so `docs/traceability.toml` can point at both. The upstream suite is the
behavioural specification; no upstream code is copied.

Run with `lake exe conformance`.
-/

open LeanMultipart

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_multipart.py::test_x`. -/
  upstream : String
  name : String
  run : IO Bool

/-! ## Helpers -/

def hexNib (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87

def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (hexNib cs[2 * i]! * 16 + hexNib cs[2 * i + 1]!).toUInt8
  return out

def bs (s : String) : ByteArray := s.toUTF8

def bnd (s : String) : Boundary :=
  match Boundary.ofBytes? s.toUTF8 with
  | some b => b
  | none => ⟨⟨#[98]⟩, by decide⟩

def eqB (a b : ByteArray) : Bool := a.data == b.data

def optEqB (a : Option ByteArray) (b : Option String) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => eqB x (bs y)
  | _, _ => false

/-- A multipart config with `maxSize := n` (`n ≥ 1`). -/
def mpMax (n : Nat) : MultipartConfig :=
  if h : 0 < n then { maxSize := some n, h_maxSize := fun m hm => by cases hm; exact h } else {}

def formMax (n : Nat) : FormParserConfig :=
  if h : 0 < n then { maxBodySize := some n, h_maxBodySize := fun m hm => by cases hm; exact h } else {}

def multipartForm (boundary : String) (cfg : FormParserConfig := {}) : FormParser :=
  FormParser.ofKind cfg (.multipart (bnd boundary))

def feedChunks (p : FormParser) (chunks : List ByteArray) : FormParser :=
  chunks.foldl FormParser.write p

/-- Does an expected item match a parsed one? -/
def itemMatches (e : Fixtures.ExpItem) (i : FormItem) : Bool :=
  match i with
  | .field f => !e.isFile && eqB f.fieldName (bs e.name) && f.value.any (eqB · (unhex e.dataHex))
  | .file f => e.isFile && f.fieldName.any (eqB · (bs e.name)) && optEqB f.fileName e.fileName &&
      optEqB f.contentType e.contentType && eqB f.data (unhex e.dataHex)

/-- Upstream's `assert_field` / `assert_file`: find each expected item and
remove it. -/
def matchAll (exp : List Fixtures.ExpItem) (got : List FormItem) : Bool :=
  match exp with
  | [] => true
  | e :: es =>
    match got.findIdx? (itemMatches e) with
    | some i => matchAll es (got.eraseIdx i)
    | none => false

def checkFixture (c : Fixtures.HttpCase) (chunks : List ByteArray) : Bool :=
  let r := (feedChunks (multipartForm c.boundary) chunks).finalize
  match c.expected, r with
  | .error off, .error (.multipart e) => e.offset == off
  | .ok exp, .ok got => matchAll exp got && got.length == exp.length
  | _, _ => false

instance : Inhabited Fixtures.HttpCase := ⟨⟨"", "", "", .ok []⟩⟩

def fixture (n : String) : Fixtures.HttpCase :=
  (Fixtures.cases.find? (·.name == n)).getD default

def bytesOf (b : ByteArray) : List ByteArray := b.data.toList.map (fun c => ⟨#[c]⟩)

def qsFields (cfg : QsConfig) (chunks : List ByteArray) : Except QsError (List (String × String)) :=
  let st := chunks.foldl (fun s c => Qs.feedT cfg s c.data.toList) ({} : QsState)
  (Qs.result st).map (·.map fun f => (latin1Decode f.1, latin1Decode f.2))

def qsIs (cfg : QsConfig) (chunks : List String) (exp : List (String × String)) : IO Bool :=
  pure (match qsFields cfg (chunks.map bs) with | .ok fs => fs == exp | .error _ => false)

def optsIs (v : String) (ct : String) (exp : List (String × String)) : IO Bool :=
  let (t, o) := parseOptionsHeader (bs v)
  pure (latin1Decode t == ct && o.entries.map (fun p => (latin1Decode p.1, latin1Decode p.2)) == exp)

def optsIsB (v : ByteArray) (ct : String) (exp : List (String × String)) : IO Bool :=
  let (t, o) := parseOptionsHeader v
  pure (latin1Decode t == ct && o.entries.map (fun p => (latin1Decode p.1, latin1Decode p.2)) == exp)

def splitAll (b : ByteArray) : List (List ByteArray) :=
  (List.range (b.size - 2)).map fun i =>
    [b.extract 0 (i + 1), b.extract (i + 1) b.size]

def b64 (chunks : List String) : Except DecodeError ByteArray := do
  let mut d : Base64Decoder := {}
  for c in chunks do d ← d.write (bs c)
  d.finalize

def qp (chunks : List String) : ByteArray :=
  (chunks.foldl (fun d c => d.write (bs c)) ({} : QuotedPrintableDecoder)).finalize

def filesOf (r : Except FormError (List FormItem)) : List File :=
  match r with
  | .ok is => is.filterMap (fun | .file f => some f | _ => none)
  | .error _ => []

def fieldsOf (r : Except FormError (List FormItem)) : List Field :=
  match r with
  | .ok is => is.filterMap (fun | .field f => some f | _ => none)
  | .error _ => []

def isErr {ε α} (r : Except ε α) : Bool := match r with | .error _ => true | .ok _ => false

def epilogueHead : String :=
  "--boundary\r\nContent-Disposition: form-data; name=\"file\"; filename=\"filename.txt\"\r\n" ++
  "Content-Type: text/plain\r\n\r\nhello\r\n--boundary--"

def oneFileHello (chunks : List ByteArray) : Bool :=
  let r := (feedChunks (multipartForm "boundary") chunks).finalize
  match filesOf r with
  | [f] => eqB f.data (bs "hello")
  | _ => false

def nTimes (s : String) (n : Nat) : String := String.join (List.replicate n s)

def starletteUrl (lim : FormLimits) (body : String) : Except LimitError (List QsField) :=
  API.Starlette.parseUrlencoded lim (bs body) |>.map (·.1)

def starletteMp (lim : FormLimits) (ct : String) (body : ByteArray) : Except LimitError (List StarlettePart) :=
  API.Starlette.parseMultipartForm lim (bs ct) body |>.map (·.1)

instance {α} [BEq α] : BEq (Except QsError α) :=
  ⟨fun a b => match a, b with | .error x, .error y => x == y | .ok x, .ok y => x == y | _, _ => false⟩

/-- Compares errors only: the Starlette cases below check which error is
raised (an `ok` never equals anything here). -/
instance {α} : BEq (Except LimitError α) :=
  ⟨fun a b => match a, b with | .error x, .error y => x == y | _, _ => false⟩

/-! ## Cases -/

/-- Upstream's `NON_PARAMETRIZED_TESTS` keeps `single_field_blocks` out of
`test_http`; it is used by `test_feed_blocks` only. -/
def httpCases : List Case :=
  (Fixtures.cases.filter (·.name != "single_field_blocks")).map fun c =>
    { upstream := s!"tests/test_multipart.py::TestFormParser::test_http[{c.name}]"
      name := s!"http fixture {c.name}"
      run := pure (checkFixture c [unhex c.bodyHex]) }

def singleByteNames : List String :=
  ["almost_match_boundary", "almost_match_boundary_without_CR", "almost_match_boundary_without_LF",
   "almost_match_boundary_without_final_hyphen", "single_field_single_file", "crlf_dense_part_data"]

def singleByteCases : List Case :=
  singleByteNames.map fun n =>
    { upstream := s!"tests/test_multipart.py::TestFormParser::test_feed_single_bytes[{n}]"
      name := s!"single bytes {n}"
      run := pure (checkFixture (fixture n) (bytesOf (unhex (fixture n).bodyHex))) }

/-! ## Ported examples

Each ported example that prints is run and its output compared with
upstream's, produced by `upstream-spec/.venv/bin/python -I
tests/upstream/docs_index.py` (python-multipart 0.0.32). -/

/-- Upstream's output for `docs/index.md`'s blocks, replaying its curl sessions. -/
def docsIndexExpected : String :=
  "== simple: curl -F foo=bar ==\n200 OK\nContent-type: text/plain\n\nParsed value parameter named: foo\n\n" ++
  "== in-depth start: curl ==\n200 OK\nContent-type: text/plain\n\nHashes:\n\n" ++
  "== in-depth: curl -F file=@/tmp/test.txt ==\n200 OK\nContent-type: text/plain\n\n" ++
  "Part hash: 0b64696c0f7ddb9e3435341720988d5455b3b0f0724688f98ec8e6019af3d931\n"

def exampleCases : List Case := [
  { upstream := "docs/index.md (Quickstart: Simple Example, In-Depth Example)"
    name := "example docs/index.md output matches upstream",
    run := do
      let out ← IO.Process.output { cmd := ".lake/build/bin/docs-index" }
      if out.stdout != docsIndexExpected then IO.println s!"      got:\n{out.stdout}"
      return out.exitCode == 0 && out.stdout == docsIndexExpected }
]

/-! ## Error paths of the `IO` objects

Each case runs `parseFormStream` or `MultipartParser.create` and `write`,
and compares the outcome with upstream's line from
`tests/upstream/io_errors.py` (python-multipart 0.0.32):
`name|outcome|class|message|callbacks`. -/

def splitError (msg : String) : String × String :=
  match msg.splitOn ": " with
  | cls :: rest => (cls, ": ".intercalate rest)
  | [] => ("", msg)

def nameOf (b : ByteArray) : String := String.fromUTF8! b

/-- Our line for `parse_form(headers, BytesIO(body), …, chunk_size)`. -/
def formLine (name : String) (headers : Headers) (body : ByteArray) (chunkSize : Nat := 1048576) : IO String := do
  let got ← IO.mkRef (#[] : Array String)
  let buf ← IO.mkRef ({ data := body } : IO.FS.Stream.Buffer)
  try
    parseFormStream headers (IO.FS.Stream.ofBuffer buf)
      (fun f => got.modify (·.push (nameOf f.fieldName)))
      (fun f => got.modify (·.push ((f.fieldName.map nameOf).getD "None"))) chunkSize
    return s!"{name}|ok|||{",".intercalate (← got.get).toList}"
  catch e =>
    let (cls, msg) := splitError (toString e)
    return s!"{name}|raise|{cls}|{msg}|{",".intercalate (← got.get).toList}"

/-- Our line for `MultipartParser(boundary, {})` then a `write`. -/
def createLine (name : String) (boundary : Option ByteArray) (data : ByteArray) : IO String := do
  let p ← try MultipartParser.create boundary catch e =>
    let (cls, msg) := splitError (toString e); return s!"{name}|raise at create|{cls}|{msg}|"
  try
    discard <| p.write data
    return s!"{name}|ok|||"
  catch e =>
    let (cls, msg) := splitError (toString e); return s!"{name}|raise at write|{cls}|{msg}|"

def fields (l : String) : List String := l.splitOn "|"

/-- Same outcome, class, message and callbacks. -/
def same (ours up : String) : Bool := ours == up

/-- A multipart parse error: same outcome, class, offset (`… at N`) and
callbacks; upstream's message also names the byte. -/
def sameError (ours up : String) : Bool :=
  match fields ours, fields up with
  | [n, o, c, m, cb], [n', o', c', m', cb'] =>
    n == n' && o == o' && c == c' && cb == cb' && (m.splitOn " at ").getLast? == (m'.splitOn " at ").getLast?
  | _, _ => false

/-- As `sameError`, but no callbacks run before the error (deviation 6:
`parseFormStream` calls them once the body is read; upstream calls them for
the items before the error). -/
def sameErrorNoCallbacks (ours up : String) : Bool :=
  match fields up with
  | [n, o, c, m, _] => sameError ours s!"{n}|{o}|{c}|{m}|"
  | _ => false

def urlCt : Headers := [("Content-Type", bs "application/x-www-form-urlencoded")]
def badHeaderBody : ByteArray :=
  bs "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nx\r\n--B\r\nBad Header: y\r\n\r\nz\r\n--B--\r\n"
def clBody : ByteArray := bs (nTimes "a=b&c=d" 5)

def ioCase (name upstream : String) (ours : IO String) (agree : String → String → Bool := same) : Case :=
  { upstream := s!"python_multipart parse_form / MultipartParser (tests/upstream/io_errors.py: {upstream})"
    name := s!"io: {name}",
    run := do
      let o ← ours
      unless agree o upstream do IO.println s!"      ours:     {o}\n      upstream: {upstream}"
      return agree o upstream }

def ioCases : List Case :=
  [ ioCase "bad header after a field (no callbacks before the error, deviation 6)"
      "bad header after a field|raise|MultipartParseError|Found invalid character 32 in header at 60|a"
      (formLine "bad header after a field" [("Content-Type", bs "multipart/form-data; boundary=B")] badHeaderBody)
      sameErrorNoCallbacks,
    ioCase "chunk_size 0" "chunk_size 0|raise|ValueError|chunk_size must be a positive number, not 0|"
      (formLine "chunk_size 0" urlCt (bs "a=b") 0),
    ioCase "no boundary" "no boundary|raise|FormParserError|No boundary given|"
      (formLine "no boundary" [("Content-Type", bs "multipart/form-data")] .empty),
    ioCase "no Content-Type" "no Content-Type|raise|ValueError|No Content-Type header given!|"
      (formLine "no Content-Type" [] .empty),
    ioCase "create b'B' then a write that raises"
      "create b'B'|raise at write|MultipartParseError|Found invalid character 32 in header at 8|"
      (createLine "create b'B'" (some (bs "B")) (bs "--B\r\nBad Header: y\r\n\r\nz\r\n--B--\r\n")) sameError,
    -- upstream's constructor takes len(None): a TypeError, with Python's message
    ioCase "create None raises a TypeError"
      "create None|raise at create|TypeError|object of type 'NoneType' has no len()|"
      (createLine "create None" none .empty),
    -- deviation 4: b'' is not a Boundary, so create raises; upstream fails at the first write
    ioCase "create b'' raises at create (deviation 4), upstream at write"
      "create b''|raise at write|MultipartParseError|Did not find CR at end of boundary (2)|"
      (createLine "create b''" (some .empty) (bs "--B\r\n"))
      (fun o u => (fields o).take 3 == ["create b''", "raise at create", "ValueError"] && (fields u)[1]! == "raise at write") ] ++
  ([("-1", "Content-Length '-1'|raise|ValueError|Content-Length must be non-negative|"),
    ("x", "Content-Length 'x'|raise|ValueError|invalid literal for int() with base 10: b'x'|"),
    ("+3", "Content-Length '+3'|ok|||a"),
    (" 3 ", "Content-Length ' 3 '|ok|||a"),
    ("3_0", "Content-Length '3_0'|ok|||a,c,c,c,c"),
    ("1__0", "Content-Length '1__0'|raise|ValueError|invalid literal for int() with base 10: b'1__0'|"),
    ("_3", "Content-Length '_3'|raise|ValueError|invalid literal for int() with base 10: b'_3'|"),
    ("3_", "Content-Length '3_'|raise|ValueError|invalid literal for int() with base 10: b'3_'|"),
    ("-0", "Content-Length '-0'|ok|||"),
    ("", "Content-Length ''|raise|ValueError|invalid literal for int() with base 10: b''|"),
    ("\t3\n", "Content-Length '\\t3\\n'|ok|||a")].map fun (cl, up) =>
    ioCase s!"Content-Length {repr cl}" up
      (formLine ((fields up).headD "") (urlCt ++ [("Content-Length", bs cl)]) clBody))

/-- Python's 4300-digit limit on `int()` (golden lines from `io_errors.py`). -/
def ioDigitCases : List Case :=
  [
    ("4300 digits", nTimes "1" 4300,
      "Content-Length 4300 digits|ok|||a,c,c,c,c,c"),
    ("4301 digits", nTimes "1" 4301,
      "Content-Length 4301 digits|raise|ValueError|Exceeds the limit (4300 digits) for integer string conversion: value has 4301 digits; use sys.set_int_max_str_digits() to increase the limit|"),
    ("4301 digits with sign and underscores", "-" ++ nTimes "1_" 4300 ++ "1",
      "Content-Length 4301 digits with sign and underscores|raise|ValueError|Exceeds the limit (4300 digits) for integer string conversion: value has 4301 digits; use sys.set_int_max_str_digits() to increase the limit|"),
    ("5000 digits then x", nTimes "1" 5000 ++ "x",
      "Content-Length 5000 digits then x|raise|ValueError|invalid literal for int() with base 10: b'111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111|")
  ].map fun (name, cl, up) =>
    ioCase s!"Content-Length {name}" up (formLine ((fields up).headD "") (urlCt ++ [("Content-Length", bs cl)]) clBody)

/-! ## Starlette's field decoding

`tests/upstream/unquote_golden.txt` holds CPython's
`unquote_plus(raw.decode("latin-1"))` for 812 seeded inputs (escapes,
`+`, invalid and truncated UTF-8, Latin-1 bytes), written by
`tests/upstream/unquote_golden.py`. -/

def decodeCases : List Case :=
  [{ upstream := "starlette formparsers.py FormParser.on_field_name (max_part_size on the name)"
     name := "starlette urlencoded: a 1 MiB + 1 name is refused at the default limits",
     run := pure (match API.Starlette.parseUrlencodedForm {} (bs (nTimes "x" (1024 * 1024 + 1) ++ "=1")) with
       | .error (.fieldTooLarge _) => true | _ => false) },
   { upstream := "starlette formparsers.py FormParser (a name at the limit is accepted)"
     name := "starlette urlencoded: a 1 MiB name is accepted and decoded",
     run := pure (match API.Starlette.parseUrlencodedForm {} (bs (nTimes "a+b%41" (1024 * 1024 / 6) ++ "=1")) with
       | .ok items => items.val == [(nTimes "a bA" (1024 * 1024 / 6), "1")] | _ => false) },
   { upstream := "starlette formparsers.py FormParser.parse (unquote_plus(field.decode(\"latin-1\")))"
     name := "starlette urlencoded: '+' and raw bytes >= 0x80 in a 1 MiB name and value",
     run := pure (match API.Starlette.parseUrlencodedForm {} (bs (nTimes "hello+caf\u00e9" 50000 ++ "=" ++ nTimes "a+b\u00ff%41" 50000)) with
       | .ok items => items.val == [(nTimes "hello caf\u00c3\u00a9" 50000, nTimes "a b\u00c3\u00bfA" 50000)] | _ => false) },
   { upstream := "starlette formparsers.py FormParser.parse (unquote_plus(field.decode(\"latin-1\"))), tests/upstream/unquote_golden.py"
     name := "unquotePlusLatin1 = CPython unquote_plus on 812 golden inputs",
     run := do
       let text ← IO.FS.readFile "tests/upstream/unquote_golden.txt"
       let mut ok := true
       let mut n := 0
       for line in text.splitOn "\n" do
         match line.splitOn " " with
         | [raw, want] =>
           n := n + 1
           let got := (API.Starlette.decodeField (unhex raw, .empty)).1.toUTF8
           unless eqB got (unhex want) do
             IO.println s!"      {raw}: got {got.toList}, want {(unhex want).toList}"
             ok := false
         | _ => pure ()
       return ok && n == 812 }]

/-- The body of Starlette's `test_multipart_request_mixed_files_and_data`. -/
def mixedBody : ByteArray := bs ("--a7f7ac8d4e2e437c877bb7b8d7cc549c\r\n" ++
  "Content-Disposition: form-data; name=\"field0\"\r\n\r\nvalue0\r\n" ++
  "--a7f7ac8d4e2e437c877bb7b8d7cc549c\r\n" ++
  "Content-Disposition: form-data; name=\"file\"; filename=\"file.txt\"\r\nContent-Type: text/plain\r\n\r\n" ++
  "<file content>\r\n" ++
  "--a7f7ac8d4e2e437c877bb7b8d7cc549c\r\n" ++
  "Content-Disposition: form-data; name=\"field1\"\r\n\r\nvalue1\r\n" ++
  "--a7f7ac8d4e2e437c877bb7b8d7cc549c--\r\n")

/-- Feed `body` in chunks of `n` bytes, keeping each chunk's events. -/
def feedAll (p : Starlette.MultipartStream) (body : ByteArray) (n : Nat) :
    Except LimitError (Starlette.MultipartStream × List (Array Starlette.PartEvent)) := do
  let mut p := p
  let mut out := #[]
  for i in [0:(body.size + n - 1) / n] do
    let (p', evs) ← p.feed (body.extract (i * n) (i * n + n))
    p := p'; out := out.push evs
  return (p, out.toList)

/-- A stream for boundary `B`. -/
def streamB : Starlette.MultipartStream := .new ⟨⟨#[66]⟩, by decide⟩

def evTag : Starlette.PartEvent → String
  | .part i => s!"part:{String.fromUTF8! i.name}"
  | .data b => s!"data:{String.fromUTF8! b}"
  | .partEnd => "end"

/-- Cases particular to the incremental parser: what each `feed` reports.
Starlette's `MultiPartParser.parse` handles python-multipart's callbacks per
chunk (`on_headers_finished` opens the part, `on_part_data` hands the bytes
over, `on_part_end` closes it); these check the events in that order and that
data is handed over as soon as it is known not to be a delimiter. -/
def streamCases : List Case := [
  { upstream := "starlette formparsers.py MultiPartParser.parse (on_headers_finished, on_part_data, on_part_end)"
    name := "stream: events for the mixed body, in one chunk",
    run := pure (match Starlette.MultipartStream.create (bs "multipart/form-data; boundary=a7f7ac8d4e2e437c877bb7b8d7cc549c") with
      | .ok p => match feedAll p mixedBody mixedBody.size with
        | .ok (p', [evs]) => p'.ended && evs.toList.map evTag ==
            ["part:field0", "data:value0", "end", "part:file", "data:<file content>", "end", "part:field1", "data:value1", "end"]
        | _ => false
      | .error _ => false) },
  { upstream := "starlette formparsers.py MultiPartParser.parse (on_part_data per chunk)"
    name := "stream: data is handed over chunk by chunk, holding back only a possible delimiter",
    run := pure (match feedAll (streamB) (bs ("--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\n" ++
          "hello\r\n-") ++ bs ("-world\r\n--B--\r\n")) 57 with
      | .ok (p', chunks) => p'.ended && chunks.map (·.toList.map evTag) ==
          [["part:a", "data:hello"], ["data:\r\n--world", "end"]]
      | .error _ => false) },
  { upstream := "starlette formparsers.py MultiPartParser.parse (stops at the first limit crossed)"
    name := "stream: a limit stops the feed that crosses it",
    run := pure (match Starlette.MultipartStream.create (bs "multipart/form-data; boundary=B") { maxFields := 1 } with
      | .ok p => match p.feed (bs "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nx\r\n") with
        | .ok (p, _) => (match p.feed (bs "--B\r\nContent-Disposition: form-data; name=\"b\"\r\n\r\nx") with
          | .error (.tooManyFields 1) => true | _ => false)
        | .error _ => false
      | .error _ => false) },
  { upstream := "starlette formparsers.py MultiPartParser.parse (epilogue ignored)"
    name := "stream: after the closing delimiter, more chunks are ignored",
    run := pure (match feedAll (streamB)
          (bs "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nv\r\n--B--\r\nepilogue --B\r\n") 3 with
      | .ok (p', chunks) => p'.ended && (chunks.flatMap (·.toList.map evTag)).filter (· != "data:") != [] &&
          String.join (chunks.flatMap (·.toList.filterMap fun e => match e with | .data b => some (String.fromUTF8! b) | _ => none)) == "v"
      | .error _ => false) }
]

/-- Starlette's multipart cases, run by `mp`: the whole-buffer parser, or the
incremental `MultipartStream` fed the body in chunks (`via` names which). -/
def starletteMpCases (via : String) (mp : FormLimits → String → ByteArray → Except LimitError (List StarlettePart)) :
    List Case := [
  { upstream := "starlette tests/test_formparsers.py::test_missing_boundary_parameter"
    name := s!"starlette missing boundary{via}",
    run := pure (mp {} "multipart/form-data; charset=utf-8" (bs "x") == .error .missingBoundary) },
  { upstream := "starlette tests/test_formparsers.py::test_multipart_boundary_exceeds_limit"
    name := s!"starlette boundary too long{via}",
    run := pure (let b := nTimes "X" 257
      mp {} s!"multipart/form-data; boundary={b}" (bs s!"--{b}\r\n\r\n--{b}--\r\n") == .error .invalidMultipart) },
  { upstream := "starlette tests/test_formparsers.py::test_multipart_headers_exceed_limit"
    name := s!"starlette header count{via}",
    run := pure (mp {} "multipart/form-data; boundary=boundary"
      (bs ("--boundary\r\nContent-Disposition: form-data; name=\"field\"\r\n" ++
        String.join ((List.range 8).map (s!"X-Extra-{·}: value\r\n")) ++ "\r\nvalue\r\n--boundary--\r\n")) == .error .invalidMultipart) },
  { upstream := "starlette tests/test_formparsers.py::test_missing_name_parameter_on_content_disposition"
    name := s!"starlette missing name{via}",
    run := pure (mp {} "multipart/form-data; boundary=a7f7ac8d4e2e437c877bb7b8d7cc549c"
      (bs "--a7f7ac8d4e2e437c877bb7b8d7cc549c\r\nContent-Disposition: form-data; =\"field0\"\r\n\r\nvalue0\r\n") == .error .missingName) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_fields_raise"
    name := s!"starlette too many fields{via}",
    run := pure (mp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFields 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_files_raise"
    name := s!"starlette too many files{via}",
    run := pure (mp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\"; filename=\"F{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_files_single_field_raise"
    name := s!"starlette too many files, one field name{via}",
    run := pure (mp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N\"; filename=\"F{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_multipart_request_mixed_files_and_data"
    name := s!"starlette mixed files and data{via}",
    run := pure (match mp {} "multipart/form-data; boundary=a7f7ac8d4e2e437c877bb7b8d7cc549c" mixedBody with
      | .ok [f0, f, f1] =>
        eqB f0.name (bs "field0") && eqB f0.data (bs "value0") && !f0.isFile &&
        eqB f.name (bs "file") && (f.filename.any (eqB · (bs "file.txt"))) && eqB f.data (bs "<file content>") &&
        (f.headers.any fun h => eqB h.1 (bs "content-type") && eqB h.2 (bs "text/plain")) &&
        eqB f1.name (bs "field1") && eqB f1.data (bs "value1")
      | _ => false) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_files_and_fields_raise"
    name := s!"starlette too many files and fields{via}",
    run := pure (mp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i =>
        s!"--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_fields_is_customizable_low_raises"
    name := s!"starlette max_fields=1{via}",
    run := pure (mp { maxFields := 1 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFields 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_files_is_customizable_low_raises"
    name := s!"starlette max_files=1{via}",
    run := pure (mp { maxFiles := 1 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_fields_is_customizable_high"
    name := s!"starlette max_fields=2000{via}",
    run := pure (match mp { maxFields := 2000, maxFiles := 2000 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2000).map fun i =>
        s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n") ++ "--B--\r\n")) with
      | .ok ps => ps.length == 4000 && (ps.getLast?.any fun p => p.isFile && p.data.size == 0)
      | .error _ => false) },
  { upstream := "starlette tests/test_formparsers.py::test_max_part_size_exceeds_limit"
    name := s!"starlette part too large{via}",
    run := pure (let b := "------------------------4K1ON9fZkj9uCUmqLHRbbR"
      mp {} s!"multipart/form-data; boundary={b}"
        (bs (s!"--{b}\r\nContent-Disposition: form-data; name=\"small\"\r\n\r\nsmall content\r\n--{b}\r\n" ++
          "Content-Disposition: form-data; name=\"large\"\r\n\r\n" ++ nTimes "x" (1024 * 1024 + 1) ++ s!"\r\n--{b}--\r\n"))
        == .error (.partTooLarge (1024 * 1024))) },
  { upstream := "starlette formparsers.py MultiPartParser (counts at headers, size on data)"
    name := s!"starlette multipart: the first limit crossed is reported{via}",
    run := pure (
      mp { maxFields := 1, maxPartSize := 3 } "multipart/form-data; boundary=B"
        (bs "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nxxxxx\r\n--B\r\nContent-Disposition: form-data; name=\"b\"\r\n\r\nx\r\n--B--\r\n")
        == .error (.partTooLarge 3) &&
      mp { maxFields := 1, maxPartSize := 3 } "multipart/form-data; boundary=B"
        (bs "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nx\r\n--B\r\nContent-Disposition: form-data; name=\"b\"\r\n\r\nxxxxx\r\n--B--\r\n")
        == .error (.tooManyFields 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_part_size_exceeds_custom_limit"
    name := s!"starlette part too large (10KB){via}",
    run := pure (let b := "------------------------4K1ON9fZkj9uCUmqLHRbbR"
      mp { maxPartSize := 10240 } s!"multipart/form-data; boundary={b}"
        (bs (s!"--{b}\r\nContent-Disposition: form-data; name=\"small\"\r\n\r\nsmall content\r\n--{b}\r\n" ++
          "Content-Disposition: form-data; name=\"large\"\r\n\r\n" ++ nTimes "x" 10241 ++ s!"\r\n--{b}--\r\n"))
        == .error (.partTooLarge 10240)) }
]

/-- `MultipartStream` fed `body` in chunks of `n` bytes, through the public API. -/
def streamMp (n : Nat) (lim : FormLimits) (ct : String) (body : ByteArray) : Except LimitError (List StarlettePart) :=
  let chunks := (List.range ((body.size + n - 1) / n)).map fun i => body.extract (i * n) (i * n + n)
  API.Starlette.parseMultipartChunks lim (bs ct) chunks |>.map (·.1)

def cases : List Case := httpCases ++ singleByteCases ++ exampleCases ++ ioCases ++ ioDigitCases ++ decodeCases ++
    starletteMpCases "" starletteMp ++ starletteMpCases " (streamed, 1-byte chunks)" (streamMp 1) ++
    starletteMpCases " (streamed, 7-byte chunks)" (streamMp 7) ++
    starletteMpCases " (streamed, 64 KiB chunks)" (streamMp 65536) ++ streamCases ++ [
  -- Querystring parser
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_simple_querystring"
    name := "querystring simple", run := qsIs {} ["foo=bar"] [("foo", "bar")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_querystring_blank_beginning"
    name := "querystring blank beginning", run := qsIs {} ["&foo=bar"] [("foo", "bar")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_querystring_blank_end"
    name := "querystring blank end", run := qsIs {} ["foo=bar&"] [("foo", "bar")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_querystring_trailing_bare_field_name"
    name := "querystring trailing bare name", run := qsIs {} ["foo=bar&baz"] [("foo", "bar"), ("baz", "")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_querystring_only_bare_field_name"
    name := "querystring only bare name", run := qsIs {} ["foo"] [("foo", "")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_multiple_querystring"
    name := "querystring multiple", run := qsIs {} ["foo=bar&asdf=baz"] [("foo", "bar"), ("asdf", "baz")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_streaming_simple"
    name := "querystring streaming", run := qsIs {} ["foo=bar&", "asdf=baz"] [("foo", "bar"), ("asdf", "baz")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_streaming_break"
    name := "querystring streaming break",
    run := qsIs {} ["foo=one", "two", "three", "&asd", "f=baz"] [("foo", "onetwothree"), ("asdf", "baz")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_semicolon_is_data_not_a_field_separator"
    name := "querystring semicolon is data",
    run := qsIs {} ["role=user&x=;role=admin"] [("role", "user"), ("x", ";role=admin")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_too_large_field"
    name := "querystring max size",
    run := qsIs { maxSize := some 15 } ["foo=bar&", "a=123456"] [("foo", "bar"), ("a", "12345")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_strict_parsing_pass"
    name := "querystring strict pass (all splits)",
    run := pure ((splitAll (bs "foo=bar&another=asdf")).all fun cs =>
      qsFields { strictParsing := true } cs == .ok [("foo", "bar"), ("another", "asdf")]) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_strict_parsing_fail_double_sep"
    name := "querystring strict double separator (all splits)",
    run := pure ((splitAll (bs "foo=bar&&another=asdf")).all fun cs =>
      match qsFields { strictParsing := true } cs with
      | .error e => e.kind == .duplicateAmpersand && e.offset == 8
      | .ok _ => false) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_double_sep"
    name := "querystring double separator (all splits)",
    run := pure ((splitAll (bs "foo=bar&&another=asdf")).all fun cs =>
      qsFields {} cs == .ok [("foo", "bar"), ("another", "asdf")]) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_strict_parsing_fail_no_value"
    name := "querystring strict no value",
    run := pure (match qsFields { strictParsing := true } [bs "foo=bar&blank&another=asdf"] with
      | .error e => e.kind == .missingEquals && e.offset == 8 | .ok _ => false) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_success_no_value"
    name := "querystring no value",
    run := qsIs {} ["foo=bar&blank&another=asdf"] [("foo", "bar"), ("blank", ""), ("another", "asdf")] },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_no_callbacks"
    name := "querystring write returns length",
    run := pure (match (QuerystringParser.new).write (bs "foo=bar") with | .ok (_, _, n) => n == 7 | .error _ => false) },
  { upstream := "tests/test_multipart.py::test_parser_states_remain_enum_members"
    name := "querystring ends in field data",
    run := pure (match (QuerystringParser.new).write (bs "field=value") with | .ok (p, _, _) => p.st.phase == .fieldData | .error _ => false) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_invalid_max_size"
    name := "max_size below 1 cannot be configured",
    run := pure ((mpMax 0).maxSize.isNone) },
  -- parse_options_header
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_simple"
    name := "options simple", run := optsIs "application/json" "application/json" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_blank"
    name := "options blank", run := optsIs "" "" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_single_param"
    name := "options single param", run := optsIs "application/json;par=val" "application/json" [("par", "val")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_single_param_with_spaces"
    name := "options param with spaces", run := optsIs "application/json;     par=val" "application/json" [("par", "val")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_multiple_params"
    name := "options multiple params",
    run := optsIs "application/json;par=val;asdf=foo" "application/json" [("par", "val"), ("asdf", "foo")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_quoted_param"
    name := "options quoted", run := optsIs "application/json;param=\"quoted\"" "application/json" [("param", "quoted")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_quoted_param_with_semicolon"
    name := "options quoted semicolon",
    run := optsIs "application/json;param=\"quoted;with;semicolons\"" "application/json" [("param", "quoted;with;semicolons")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_quoted_param_with_escapes"
    name := "options quoted escapes",
    run := optsIs "application/json;param=\"This \\\" is \\\" a \\\" quote\"" "application/json" [("param", "This \" is \" a \" quote")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_handles_ie6_bug"
    name := "options IE6 filename",
    run := optsIs "text/plain; filename=\"C:\\this\\is\\a\\path\\file.txt\"" "text/plain" [("filename", "file.txt")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_redos_attack_header"
    name := "options ReDoS header terminates",
    run := do
      let (_, o) := parseOptionsHeader (bs ("application/x-www-form-urlencoded; !=\"" ++ nTimes "\\" 2000))
      pure (o.entries.any fun p => latin1Decode p.1 == "!" && (latin1Decode p.2).startsWith "\"\\") },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_ignores_rfc_2231_extended_param"
    name := "options ignores param*", run := optsIs "text/plain; param*=us-ascii'en-us'encoded%20message" "text/plain" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_plain_param_authoritative_over_extended"
    name := "options plain over extended",
    run := optsIs "form-data; name=\"comment\"; name*=utf-8''other" "form-data" [("name", "comment")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_ignores_rfc_2231_continuation_filename"
    name := "options ignores filename*0",
    run := optsIs "form-data; name=\"f\"; filename*0=\"a\"; filename*1=\"b.txt\"" "form-data" [("name", "f")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_ignores_oversized_rfc_2231_index"
    name := "options ignores oversized index",
    run := optsIs ("text/plain; filename*" ++ nTimes "1" 4301 ++ "*=utf-8''x") "text/plain" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_ignores_mixed_rfc_2231_continuations"
    name := "options ignores mixed continuations",
    run := optsIs "text/plain; filename*=utf-8''a; filename*0*=utf-8''b" "text/plain" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_ignores_extended_param_case_insensitively"
    name := "options ignores UPPER*", run := optsIs "text/plain; UPPER*=utf-8''X" "text/plain" [] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_preserves_quoted_semicolons_and_escapes"
    name := "options quoted semicolons and escapes",
    run := optsIs "text/plain; a=\"x;y\"; b=\"esc \\\" quote\"" "text/plain" [("a", "x;y"), ("b", "esc \" quote")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_preserves_content_type_case"
    name := "options content type case", run := optsIs "Text/Plain; a=b" "Text/Plain" [("a", "b")] },
  { upstream := "tests/test_multipart.py::TestParseOptionsHeader::test_preserves_backslash_unquoting_order"
    name := "options backslash order", run := optsIs "text/plain; q=\"a\\\\b\"" "text/plain" [("q", "a\\b")] },
  -- OctetStreamParser
  { upstream := "tests/test_multipart.py::TestOctetStreamParser::test_simple"
    name := "octet stream parser simple",
    run := pure (let (p, e1, _) := (OctetStreamParser.new).write (bs "foobar")
      let e2 := p.finalize
      (e1.toList.map fun | .start => "s" | .data b => latin1Decode b | .end => "e") ++
        (e2.toList.map fun | .start => "s" | .data b => latin1Decode b | .end => "e") == ["s", "foobar", "e"]) },
  { upstream := "tests/test_multipart.py::TestOctetStreamParser::test_multiple_chunks"
    name := "octet stream parser chunks",
    run := pure (Id.run do
      let mut p := OctetStreamParser.new
      let mut out := ""
      for c in ["foo", "bar", "baz"] do
        let (p', evs, _) := p.write (bs c)
        p := p'
        for e in evs do
          if let .data b := e then out := out ++ latin1Decode b
      return out == "foobarbaz") },
  { upstream := "tests/test_multipart.py::TestOctetStreamParser::test_max_size"
    name := "octet stream parser max size",
    run := pure (let (_, evs, n) := (OctetStreamParser.new (maxSize := some 5)).write (bs "0123456789")
      n == 5 && evs.toList.any (fun | .data b => latin1Decode b == "01234" | _ => false)) },
  -- Decoders
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_simple"
    name := "base64 simple", run := pure (b64 ["Zm9vYmFy"] |>.toOption |>.any (eqB · (bs "foobar"))) },
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_bad"
    name := "base64 bad", run := pure (isErr (b64 ["Zm9v!mFy"])) },
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_split_properly"
    name := "base64 split", run := pure (b64 ["Zm9v", "YmFy"] |>.toOption |>.any (eqB · (bs "foobar"))) },
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_bad_split"
    name := "base64 bad split",
    run := pure ([1, 2, 3].all fun i => b64 [("Zm9v".take i).toString, ("Zm9v".drop i).toString] |>.toOption |>.any (eqB · (bs "foo"))) },
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_long_bad_split"
    name := "base64 long bad split",
    run := pure ([5, 6, 7].all fun i => b64 [("Zm9vYmFy".take i).toString, ("Zm9vYmFy".drop i).toString] |>.toOption |>.any (eqB · (bs "foobar"))) },
  { upstream := "tests/test_multipart.py::TestBase64Decoder::test_bad_length"
    name := "base64 bad length", run := pure (isErr (b64 ["Zm9vYmF"])) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_simple"
    name := "qp simple", run := pure (eqB (qp ["foobar"]) (bs "foobar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_escape"
    name := "qp escape", run := pure (eqB (qp ["foo=3Dbar"]) (bs "foo=bar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_newline_escape"
    name := "qp newline escape", run := pure (eqB (qp ["foo=\r\nbar"]) (bs "foobar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_only_newline_escape"
    name := "qp LF escape", run := pure (eqB (qp ["foo=\nbar"]) (bs "foobar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_split_escape"
    name := "qp split escape", run := pure (eqB (qp ["foo=3", "Dbar"]) (bs "foo=bar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_split_newline_escape_1"
    name := "qp split newline 1", run := pure (eqB (qp ["foo=\r", "\nbar"]) (bs "foobar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_with_split_newline_escape_2"
    name := "qp split newline 2", run := pure (eqB (qp ["foo=", "\r\nbar"]) (bs "foobar")) },
  { upstream := "tests/test_multipart.py::TestQuotedPrintableDecoder::test_not_aligned"
    name := "qp not aligned",
    run := pure (eqB (qp ["=3AX"]) (bs ":X") && eqB (qp ["=3", "AX"]) (bs ":X") && eqB (qp ["q=3AX"]) (bs "q:X")) },
  -- FormParser, multipart
  { upstream := "tests/test_multipart.py::test_content_transfer_encoding_is_case_insensitive"
    name := "CTE case-insensitive",
    run := pure (["base64", "BASE64", "Base64"].all fun cte =>
      let data := bs ("----boundary\r\nContent-Disposition: form-data; name=\"file\"; filename=\"test.txt\"\r\n" ++
        "Content-Type: text/plain\r\nContent-Transfer-Encoding: " ++ cte ++ "\r\n\r\nVGVzdA==\r\n----boundary--\r\n")
      match filesOf (feedChunks (multipartForm "--boundary") [data]).finalize with
      | [f] => eqB f.data (bs "Test") | _ => false) },
  { upstream := "tests/test_multipart.py::test_finalizes_transfer_encoding_before_callback"
    name := "QP finalised before callback",
    run := pure (match fieldsOf (feedChunks (multipartForm "b") [bs ("--b\r\nContent-Disposition: form-data; name=\"f\"\r\n" ++
        "Content-Transfer-Encoding: quoted-printable\r\n\r\n=4\r\n--b--\r\n")]).finalize with
      | [f] => f.value.any (eqB · (bs "=4")) | _ => false) },
  { upstream := "tests/test_multipart.py::test_parser_states_remain_enum_members"
    name := "empty message ends",
    run := pure (match (MultipartParser.new (bnd "boundary")).write (bs "--boundary--\r\n") with
      | .ok (p, _, _) => p.ended | .error _ => false) },
  { upstream := "tests/test_multipart.py::test_multipart_opening_boundary_max_size"
    name := "opening boundary across max size",
    run := do
      let data := bs "--boundary\r\n\r\nvalue\r\n--boundary--"
      let p := MultipartParser.new (bnd "boundary") { maxSize := some 9 }
      let .ok (p, ev1, n1) := p.write data | pure false
      let p := { p with cx := { p.cx with cfg := { maxSize := some (data.size + 1), h_maxSize := by intro m h; cases h; omega } } }
      let .ok (_, ev2, n2) := p.write (data.extract 9 data.size) | pure false
      let names := (ev1 ++ ev2).toList.filterMap fun
        | .partBegin => some "begin" | MultipartEvent.end => some "end" | _ => none
      pure (n1 == 9 && n2 == data.size - 9 && names == ["begin", "end"]) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_random_splitting"
    name := "every two-way split",
    run := pure ((splitAll (unhex (fixture "single_field_single_file").bodyHex)).all fun cs =>
      checkFixture (fixture "single_field_single_file") cs) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_feed_blocks"
    name := "fixed-size blocks after a skip",
    run := pure (Id.run do
      let data := unhex (fixture "single_field_blocks").bodyHex
      let mut ok := true
      for c in [1:data.size + 1] do
        for d in [0:c] do
          let mut chunks := [data.extract 0 d]
          let mut x := d
          while x < data.size do
            chunks := chunks ++ [data.extract x (x + c)]
            x := x + c
          let r := (feedChunks (multipartForm "boundary") chunks).finalize
          ok := ok && (match fieldsOf r with
            | [f] => f.value.any (eqB · (bs "0123456789ABCDEFGHIJ0123456789ABCDEFGHIJ")) | _ => false)
      return ok) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_file_content_type_header"
    name := "file content type",
    run := pure (match filesOf (feedChunks (multipartForm "b8825ae386be4fdc9644d87e392caad3")
        [unhex (fixture "header_with_number").bodyHex]).finalize with
      | [f] => optEqB f.contentType (some "text/plain; charset=utf-8") | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_field_content_type_header"
    name := "field without content type",
    run := pure (match fieldsOf (feedChunks (multipartForm "----WebKitFormBoundaryTkr3kCBQlBe1nrhc")
        [unhex (fixture "single_field").bodyHex]).finalize with
      | [f] => f.contentType.isNone | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_bad_start_boundary"
    name := "bad start boundary",
    run := pure (["--boundary\rfoobar", "--boundaryfoobar", "--Boundary\r\nfoobar"].all fun d =>
      isErr (feedChunks (multipartForm "boundary") [bs d]).finalize) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_multipart_header_count_limit"
    name := "header count limit",
    run := pure (match (feedChunks (multipartForm "poc") [bs ("--poc\r\nContent-Disposition: form-data; name=\"x\"\r\n" ++ nTimes "X-A: 1\r\n" 8)]).finalize with
      | .error (.multipart e) => e.kind == .headerCountExceeded | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_multipart_header_size_limit"
    name := "header size limit",
    run := pure (match (feedChunks (multipartForm "poc") [bs ("--poc\r\nContent-Disposition: form-data; name=\"x\"\r\nX-A: " ++ nTimes "a" (4096 + 124))]).finalize with
      | .error (.multipart e) => e.kind == .headerSizeExceeded | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_octet_stream"
    name := "octet stream",
    run := pure (match (feedChunks (FormParser.ofKind {} .octetStream (some (bs "foo.txt"))) [bs "test", bs "1234"]).finalize with
      | .ok [.file f] => eqB f.data (bs "test1234") && optEqB f.fileName (some "foo.txt") | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_querystring"
    name := "form parser urlencoded",
    run := pure (["application/x-www-form-urlencoded", "application/x-url-encoded"].all fun ct =>
      match FormKind.select ct none with
      | .ok k => match fieldsOf (feedChunks (FormParser.ofKind {} k) [bs "foo=bar", bs "&test=asdf"]).finalize with
        | [a, b] => eqB a.fieldName (bs "foo") && a.value.any (eqB · (bs "bar")) && eqB b.fieldName (bs "test") && b.value.any (eqB · (bs "asdf"))
        | _ => false
      | .error _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_bad_content_type"
    name := "unknown content type", run := pure (isErr (FormKind.select "application/bad" none)) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_no_boundary_given"
    name := "no boundary", run := pure (isErr (FormKind.select "multipart/form-data" none)) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_bad_content_transfer_encoding"
    name := "bad CTE",
    run := do
      let data := bs ("----boundary\r\nContent-Disposition: form-data; name=\"file\"; filename=\"test.txt\"\r\n" ++
        "Content-Type: text/plain\r\nContent-Transfer-Encoding: badstuff\r\n\r\nTest\r\n----boundary--\r\n")
      let strict := (feedChunks (multipartForm "--boundary" { errorOnBadCte := true }) [data]).finalize
      let lax := (feedChunks (multipartForm "--boundary") [data]).finalize
      pure (isErr strict && (match filesOf lax with | [f] => eqB f.data (bs "Test") | _ => false)) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_bad_content_disposition"
    name := "missing field name",
    run := pure (match (feedChunks (multipartForm "--boundary") [bs ("----boundary\r\nContent-Disposition: form-data;\r\n" ++
        "Content-Type: text/plain\r\n\r\nTest\r\n----boundary--\r\n")]).finalize with
      | .error .missingFieldName => true | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_handles_None_fields"
    name := "urlencoded None fields",
    run := pure (match fieldsOf (feedChunks (FormParser.ofKind {} .urlencoded) [bs "foo=bar&another&baz=asdf"]).finalize with
      | [a, b, c] => a.value.any (eqB · (bs "bar")) && b.value.isNone && eqB b.fieldName (bs "another") && c.value.any (eqB · (bs "asdf"))
      | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_multipart_parser_preamble_before_first_boundary"
    name := "preamble skipped",
    run := pure (oneFileHello [bs ("\r\nignored preamble\r\n" ++ epilogueHead)] &&
      oneFileHello [bs (nTimes "\r\n" 5000 ++ epilogueHead)] &&
      oneFileHello [bs (nTimes "\r\n" 5000), bs epilogueHead]) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_multipart_parser_data_after_last_boundary"
    name := "data after the last boundary",
    run := pure (oneFileHello [bs (epilogueHead ++ nTimes "-" 50000 ++ "\r\n")]) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_multipart_parser_ignores_epilogue"
    name := "epilogue ignored",
    run := pure (oneFileHello [bs (epilogueHead ++ "\r\n")] && oneFileHello [bs (epilogueHead ++ "\r"), bs "\n"] &&
      oneFileHello [bs epilogueHead, bs "\r\n"] &&
      oneFileHello [bs (epilogueHead ++ "\r\n--boundary\r\nthis is not a valid header\r\n\r\nnot a real part")]) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_max_size_multipart"
    name := "multipart max size",
    run := do
      let data := unhex (fixture "single_field_single_file").bodyHex
      let p := MultipartParser.new (bnd "boundary") (mpMax (data.size / 2))
      pure (match p.write data with | .ok (_, _, n) => n == data.size / 2 | .error _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_max_size_form_parser"
    name := "form parser max body size",
    run := do
      let data := unhex (fixture "single_field_single_file").bodyHex
      let p := (multipartForm "boundary" (formMax (data.size / 2))).write data
      pure (match p with | .mp _ _ st => st.pos == data.size / 2 | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_octet_stream_max_size"
    name := "octet stream max size",
    run := pure (match (feedChunks (FormParser.ofKind { maxBodySize := some 10 } .octetStream (some (bs "foo.txt"))) [bs "0123456789012345689"]).finalize with
      | .ok [.file f] => eqB f.data (bs "0123456789") | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_boundary_too_long"
    name := "boundary length 256 / 257",
    run := pure ((Boundary.ofBytes? (bs (nTimes "x" 257))).isNone && (Boundary.ofBytes? (bs (nTimes "x" 256))).isSome) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_header_begin_callback"
    name := "header_begin fired per header",
    run := do
      let data := unhex (fixture "single_field_single_file").bodyHex
      let .ok (_, evs, n) := (MultipartParser.new (bnd "boundary") { maxSize := some 1000 }).write data | pure false
      pure (n == data.size && (evs.toList.filter fun | .headerBegin => true | _ => false).length == 3) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_create_form_parser"
    name := "create_form_parser octet stream",
    run := pure (match createFormParser [("Content-Type", bs "application/octet-stream")] with | .ok (.octet ..) => true | _ => false) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_create_form_parser_error"
    name := "create_form_parser without content type", run := pure (isErr (createFormParser [])) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_parse_form"
    name := "parse_form octet stream",
    run := pure (match parseForm [("Content-Type", bs "application/octet-stream")] (bs "123456789012345") with
      | .ok [.file f] => f.size == 15 | _ => false) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_parse_form_content_length"
    name := "parse_form honours Content-Length",
    run := pure (match parseForm [("Content-Type", bs "application/octet-stream"), ("Content-Length", bs "10")]
        (bs "123456789012345") with
      | .ok [.file f] => f.size == 10 | _ => false) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_parse_form_negative_content_length"
    name := "parse_form rejects a negative Content-Length",
    run := pure (isErr (parseForm [("Content-Type", bs "application/octet-stream"), ("Content-Length", bs "-1")]
        (bs "123456789012345"))) },
  -- Starlette limits
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_too_many_fields_raise"
    name := "starlette urlencoded too many fields",
    run := pure (starletteUrl {} (String.intercalate "&" ((List.range 1001).map (s!"N{·}="))) == .error (.tooManyFields 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_field_exceeds_max_part_size_raise"
    name := "starlette urlencoded field too large",
    run := pure (starletteUrl {} ("field=" ++ nTimes "x" (1024 * 1024 + 1)) == .error (.fieldTooLarge (1024 * 1024))) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_field_name_exceeds_max_part_size_raise"
    name := "starlette urlencoded name too large",
    run := pure (starletteUrl {} (nTimes "x" (1024 * 1024 + 1) ++ "=value") == .error (.fieldTooLarge (1024 * 1024))) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_max_fields_is_customizable"
    name := "starlette urlencoded max_fields=1",
    run := pure (starletteUrl { maxFields := 1 } "a=1&b=2" == .error (.tooManyFields 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_max_part_size_is_customizable"
    name := "starlette urlencoded max_part_size=10KB",
    run := pure (starletteUrl { maxPartSize := 10240 } ("field=" ++ nTimes "x" 10241) == .error (.fieldTooLarge 10240)) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_limits_stop_parsing_within_a_single_chunk"
    name := "starlette urlencoded stops at the first excess",
    run := do
      let p : Starlette.UrlencodedParser := { lim := { maxFields := 10 } }
      let body := bs (String.intercalate "&" ((List.range 100000).map (s!"f{·}=")))
      let p' := p.write body
      -- stopped with the error, and only the fields up to the limit are kept
      pure (p'.error? == some (.tooManyFields 10) && p'.st.inner.fields.size == 11) },
  { upstream := "starlette tests/test_formparsers.py::test_urlencoded_limits_stop_parsing_within_a_single_chunk"
    name := "starlette urlencoded field size stops early",
    run := do
      let p : Starlette.UrlencodedParser := { lim := { maxPartSize := 1024 } }
      let p' := p.write (bs ("field=" ++ nTimes "x" (1024 * 50)))
      pure (p'.error? == some (.fieldTooLarge 1024) && p'.st.inner.value.size ≤ 1025) },
  { upstream := "starlette formparsers.py FormParser (size checked on data, count at field end)"
    name := "starlette urlencoded: the first limit crossed is reported",
    run := pure (starletteUrl { maxFields := 1, maxPartSize := 3 } "a=1&bbbb=2" == .error (.fieldTooLarge 3) &&
      starletteUrl { maxFields := 1, maxPartSize := 3 } "a=1&b=2" == .error (.tooManyFields 1)) }
]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
