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
  FormParser.new cfg (.multipart (bnd boundary))

def feedChunks (p : FormParser) (chunks : List ByteArray) : FormParser :=
  chunks.foldl FormParser.write p

/-- Does an expected item match a parsed one? -/
def itemMatches (e : Fixtures.ExpItem) (i : FormItem) : Bool :=
  match i with
  | .field f => !e.isFile && eqB f.name (bs e.name) && f.value.any (eqB · (unhex e.dataHex))
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
  pure (latin1Decode t == ct && o.map (fun p => (latin1Decode p.1, latin1Decode p.2)) == exp)

def optsIsB (v : ByteArray) (ct : String) (exp : List (String × String)) : IO Bool :=
  let (t, o) := parseOptionsHeader v
  pure (latin1Decode t == ct && o.map (fun p => (latin1Decode p.1, latin1Decode p.2)) == exp)

def splitAll (b : ByteArray) : List (List ByteArray) :=
  (List.range (b.size - 2)).map fun i =>
    [b.extract 0 (i + 1), b.extract (i + 1) b.size]

def b64 (chunks : List String) : Except DecodeError ByteArray := do
  let mut d : Base64Decoder := {}
  for c in chunks do d ← d.write (bs c)
  d.finalize

def qp (chunks : List String) : ByteArray :=
  (chunks.foldl (fun d c => d.write (bs c)) ({} : QuotedPrintableDecoder)).finalize

def filesOf (r : Except FormError (List FormItem)) : List FormFile :=
  match r with
  | .ok is => is.filterMap (fun | .file f => some f | _ => none)
  | .error _ => []

def fieldsOf (r : Except FormError (List FormItem)) : List FormField :=
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

def cases : List Case := httpCases ++ singleByteCases ++ [
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
      qsFields { strict := true } cs == .ok [("foo", "bar"), ("another", "asdf")]) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_strict_parsing_fail_double_sep"
    name := "querystring strict double separator (all splits)",
    run := pure ((splitAll (bs "foo=bar&&another=asdf")).all fun cs =>
      match qsFields { strict := true } cs with
      | .error e => e.kind == .duplicateAmpersand && e.offset == 8
      | .ok _ => false) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_double_sep"
    name := "querystring double separator (all splits)",
    run := pure ((splitAll (bs "foo=bar&&another=asdf")).all fun cs =>
      qsFields {} cs == .ok [("foo", "bar"), ("another", "asdf")]) },
  { upstream := "tests/test_multipart.py::TestQuerystringParser::test_strict_parsing_fail_no_value"
    name := "querystring strict no value",
    run := pure (match qsFields { strict := true } [bs "foo=bar&blank&another=asdf"] with
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
      pure (o.any fun p => latin1Decode p.1 == "!" && (latin1Decode p.2).startsWith "\"\\") },
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
    run := pure (match (feedChunks (FormParser.new {} .octetStream (some (bs "foo.txt"))) [bs "test", bs "1234"]).finalize with
      | .ok [.file f] => eqB f.data (bs "test1234") && optEqB f.fileName (some "foo.txt") | _ => false) },
  { upstream := "tests/test_multipart.py::TestFormParser::test_querystring"
    name := "form parser urlencoded",
    run := pure (["application/x-www-form-urlencoded", "application/x-url-encoded"].all fun ct =>
      match FormKind.select ct none with
      | .ok k => match fieldsOf (feedChunks (FormParser.new {} k) [bs "foo=bar", bs "&test=asdf"]).finalize with
        | [a, b] => eqB a.name (bs "foo") && a.value.any (eqB · (bs "bar")) && eqB b.name (bs "test") && b.value.any (eqB · (bs "asdf"))
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
    run := pure (match fieldsOf (feedChunks (FormParser.new {} .urlencoded) [bs "foo=bar&another&baz=asdf"]).finalize with
      | [a, b, c] => a.value.any (eqB · (bs "bar")) && b.value.isNone && eqB b.name (bs "another") && c.value.any (eqB · (bs "asdf"))
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
    run := pure (match (feedChunks (FormParser.new { maxBodySize := some 10 } .octetStream (some (bs "foo.txt"))) [bs "0123456789012345689"]).finalize with
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
    run := pure (match createFormParser (some (bs "application/octet-stream")) with | .ok (.octet ..) => true | _ => false) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_create_form_parser_error"
    name := "create_form_parser without content type", run := pure (isErr (createFormParser none)) },
  { upstream := "tests/test_multipart.py::TestHelperFunctions::test_parse_form"
    name := "parse_form octet stream",
    run := pure (match parseFormBody {} .octetStream (bs "123456789012345") with
      | .ok [.file f] => f.data.size == 15 | _ => false) },
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
  { upstream := "starlette tests/test_formparsers.py::test_missing_boundary_parameter"
    name := "starlette missing boundary",
    run := pure (starletteMp {} "multipart/form-data; charset=utf-8" (bs "x") == .error .missingBoundary) },
  { upstream := "starlette tests/test_formparsers.py::test_multipart_boundary_exceeds_limit"
    name := "starlette boundary too long",
    run := pure (let b := nTimes "X" 257
      starletteMp {} s!"multipart/form-data; boundary={b}" (bs s!"--{b}\r\n\r\n--{b}--\r\n") == .error .invalidMultipart) },
  { upstream := "starlette tests/test_formparsers.py::test_multipart_headers_exceed_limit"
    name := "starlette header count",
    run := pure (starletteMp {} "multipart/form-data; boundary=boundary"
      (bs ("--boundary\r\nContent-Disposition: form-data; name=\"field\"\r\n" ++
        String.join ((List.range 8).map (s!"X-Extra-{·}: value\r\n")) ++ "\r\nvalue\r\n--boundary--\r\n")) == .error .invalidMultipart) },
  { upstream := "starlette tests/test_formparsers.py::test_missing_name_parameter_on_content_disposition"
    name := "starlette missing name",
    run := pure (starletteMp {} "multipart/form-data; boundary=a7f7ac8d4e2e437c877bb7b8d7cc549c"
      (bs "--a7f7ac8d4e2e437c877bb7b8d7cc549c\r\nContent-Disposition: form-data; =\"field0\"\r\n\r\nvalue0\r\n") == .error .missingName) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_fields_raise"
    name := "starlette too many fields",
    run := pure (starletteMp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFields 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_files_raise"
    name := "starlette too many files",
    run := pure (starletteMp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\"; filename=\"F{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_too_many_files_and_fields_raise"
    name := "starlette too many files and fields",
    run := pure (starletteMp {} "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 1001).map fun i =>
        s!"--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1000)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_fields_is_customizable_low_raises"
    name := "starlette max_fields=1",
    run := pure (starletteMp { maxFields := 1 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFields 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_files_is_customizable_low_raises"
    name := "starlette max_files=1",
    run := pure (starletteMp { maxFiles := 1 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2).map fun i => s!"--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n"))) == .error (.tooManyFiles 1)) },
  { upstream := "starlette tests/test_formparsers.py::test_max_fields_is_customizable_high"
    name := "starlette max_fields=2000",
    run := pure (match starletteMp { maxFields := 2000, maxFiles := 2000 } "multipart/form-data; boundary=B"
      (bs (String.join ((List.range 2000).map fun i =>
        s!"--B\r\nContent-Disposition: form-data; name=\"N{i}\";\r\n\r\n\r\n--B\r\nContent-Disposition: form-data; name=\"F{i}\"; filename=\"F{i}\";\r\n\r\n\r\n") ++ "--B--\r\n")) with
      | .ok ps => ps.length == 4000 && (ps.getLast?.any fun p => p.isFile && p.data.size == 0)
      | .error _ => false) },
  { upstream := "starlette tests/test_formparsers.py::test_max_part_size_exceeds_limit"
    name := "starlette part too large",
    run := pure (let b := "------------------------4K1ON9fZkj9uCUmqLHRbbR"
      starletteMp {} s!"multipart/form-data; boundary={b}"
        (bs (s!"--{b}\r\nContent-Disposition: form-data; name=\"small\"\r\n\r\nsmall content\r\n--{b}\r\n" ++
          "Content-Disposition: form-data; name=\"large\"\r\n\r\n" ++ nTimes "x" (1024 * 1024 + 1) ++ s!"\r\n--{b}--\r\n"))
        == .error (.partTooLarge (1024 * 1024))) },
  { upstream := "starlette tests/test_formparsers.py::test_max_part_size_exceeds_custom_limit"
    name := "starlette part too large (10KB)",
    run := pure (let b := "------------------------4K1ON9fZkj9uCUmqLHRbbR"
      starletteMp { maxPartSize := 10240 } s!"multipart/form-data; boundary={b}"
        (bs (s!"--{b}\r\nContent-Disposition: form-data; name=\"small\"\r\n\r\nsmall content\r\n--{b}\r\n" ++
          "Content-Disposition: form-data; name=\"large\"\r\n\r\n" ++ nTimes "x" 10241 ++ s!"\r\n--{b}--\r\n"))
        == .error (.partTooLarge 10240)) }
]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
