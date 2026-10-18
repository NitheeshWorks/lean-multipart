# Contributing to lean-multipart

`README.md` covers usage. This file covers the architecture, the verification
rules, what is tested rather than proved, the deviations from upstream, and
the conventions. Keep it current when the code changes.

## Architecture

`LeanMultipart/` is layered bottom-up; each layer imports only the ones
below it.

| Directory | Holds |
|---|---|
| `DataTypes/` | structures and inductives; invariants are fields (`Boundary.h_valid`, `QsConfig.h_maxSize`, …) |
| `Theory/` | the two general theories: `Machine.lean` (byte machines and chunking) and `Codec.lean` (the `Reads` judgement and its combinators) |
| `RepoImpl/` | executable definitions; total, structural recursion or `termination_by` |
| `Specifications/` | the headline properties, stated in `Prop` about public functions |
| `Proofs/` | the theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer |
| `APIs/` | functions whose types carry their postconditions (`LeanMultipart.API`) |

There is no effect module: every function is pure.

### The parsers are byte machines

`Qs.step` (querystring) and `Mp.step` (multipart) are transition functions
on one byte, mirroring upstream's `QuerystringState` / `MultipartState`.
Feeding input is a left fold (`Machine.feed`), truncated at `max_size`
(`Machine.feedT`) and run as an array fold (`Machine.feedA`). Everything
about chunking is proved once in `Theory/Machine.lean`:

* `Machine.feedT_append`, `Machine.feedChunks_eq`: feeding chunks is feeding
  their concatenation;
* `Machine.feed_forget`, `Machine.foldl_forget`: a parser that forgets
  buffers the transition never reads (reported fields, flushed data) runs the
  same machine.

The callback parsers `QuerystringParser` and `MultipartParser` step the same
machines, derive upstream's callbacks from each transition, and forget what
they report, so they stream in memory bounded by the chunk. Their headline
theorems (`QuerystringParser.parseChunks_eq`, `MultipartParser.parseChunks_eq`
in `Proofs/Stream.lean`) say that collecting the callbacks as upstream's
`FormParser` does gives the whole-buffer result for every split of the input.
The proofs are an invariant between the whole-buffer state, the streaming
state, and what the collector has assembled, checked byte by byte.

### Starlette's limits are machines too

Starlette raises `max_fields`, `max_files` and `max_part_size` from inside
the parser callbacks. `Starlette.urlStep` and `Starlette.mpStep` wrap the
querystring and multipart steps with the same checks (a field's name and
value on every byte; a part's name and file/field count when its headers
end; a field part's data on every byte) and move to an error that is a fixed
point. `Machine.feedAUntil` stops reading at a fixed point, and
`feedAUntil_eq` proves that equal to the full fold, so the chunking theorems
apply (`UrlencodedParser.finalize_chunks`, `MultipartFormParser.finalize_chunks`).
`Starlette.UrlInv` and `Starlette.MpInv` say that, while no error has been
raised, the retained state is within the limits; `urlencoded_bounded` and
`multipart_bounded` prove they hold after any input. The step facts they
rest on (a step adds at most the field or part it was reading) are in
`Proofs/StepFacts.lean`.

### Runs of bytes are taken at once

A `Machine` may carry a shortcut: `span s b i stop` says how many bytes from
`i` it handles all alike, and `bulk` consumes them at once. Its fields
`span_le` and `bulk_eq` require the shortcut to agree with folding `step`,
and `bytesFoldRun_eq` proves the fold with shortcuts (and early stop) equals
the plain fold, so `feedA` and `feedAUntil` use it and no theorem mentions
it. The multipart machine's shortcut is a run of part data up to the next
`CR` (`Mp.dataSpan`, `Mp.dataBulk`, appended with one `copySlice`); the
Starlette machine cuts the run before the byte that crosses
`max_part_size`, and `MultipartParser.write` uses it with its events
(`foldChunk_eq`). This took the whole 50 MB file-part parse from about 3 s
to about 150 ms.

### Starlette's field decoding, and `@[csimp]`

Starlette decodes each urlencoded name and value with
`unquote_plus(raw.decode("latin-1"))`. `unquotePlusLatin1`
(`RepoImpl/Unquote.lean`) is that algorithm as a byte machine pushing
characters onto a `String`: `+` is a space, each run of `%XY` bytes is UTF-8
with CPython's replacement rules, any other byte is its Latin-1 character.
The machine is generic in its output (`Sink`); run into a `ByteArray` of
UTF-8 with runs of plain ASCII copied at once (`plainSpan`, `plainBulk`), it
is `unquotePlusLatin1Fast`, and `Proofs/Unquote.lean` proves the two equal
and marks it `@[csimp]`, so compiled code runs the fast form while every
statement is about the specification. Scans use the same mechanism:
`scanUntil` and `scanFor` count with `Nat` in the proofs and run on `USize`
indices (`scanUntil_eq_fast`, `scanFor_eq_fast`). Agreement with CPython is
tested on 812 golden inputs (`tests/upstream/unquote_golden.py`).

### The round trips are codec instances

`Theory/Codec.lean` defines `Reads M P w Q` (from every state in `P`,
feeding `w` reaches `Q`) with one lemma per printer combinator:
`Reads.append`, `Reads.flatMap`, `Reads.sepBy`, `Reads.mono`. Each codec
proves a `Reads` fact for one token and assembles the message:

| Codec | token lemma | assembly |
|---|---|---|
| percent (`percentEncode`, `quotePlus`) | `reads_encByte`, `reads_encPlusByte` (decoder machine `decStep`) | `Reads.flatMap` |
| urlencoded (`urlencodeB`) | `Qs.reads_pair`, `Qs.reads_amp` | `Reads.sepBy` |
| multipart (`Mp.print`) | `Mp.reads_part`, `Mp.reads_next`, `Mp.reads_last` | `Reads.sepBy`, `Reads.append` |

Because a `Reads` fact holds from every state in `P`, it holds on any
continuation of the buffer, which is the `_ext` form. The Content-Disposition
round trip (`dispositionParams_formPart`, `Proofs/Options.lean`) is about
`parse_options_header`, which is not a machine; it is built from one lemma
per stage of `_parseparam` (split at `;`, group by quote parity, normalise a
piece, unquote).

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes
  the minimal hypothesis its body needs and returns the strongest useful
  statement as `{r // Post r}` or `Except Err {r // Post r}`.
* **Decidable predicates**, so the same predicate is checked at runtime
  (`API.printMultipart?`, `Boundary.ofBytes?`) and used in proofs.
* **Totality.** No `partial def`, `unsafe`, `implemented_by`, `extern`,
  `native_decide` or `bv_decide` under `LeanMultipart/`; the gate
  (`scripts/Axioms.lean`) checks every declaration. There is no
  `scripts/gate-allow.txt`: nothing needs an exception.
* **The gate.** `scripts/check.sh` runs what CI runs: build, the
  declaration checker (every theorem reaches only `propext`, `Quot.sound`,
  `Classical.choice`), `lake exe props`, `lake exe conformance`,
  `lake exe docs-index`, the traceability check; `--pbt` adds the plausible
  suite.

### Tested, not proved

Each has a property in `tests/Props.lean` or cases in
`tests/Conformance.lean`, and a `status = "tested"` row in
`docs/traceability.toml`.

| Behaviour | Why it is not proved |
|---|---|
| String-level `urlencodeStr` / `urldecodeStr` round trip | the byte-level round trip is proved; lifting it needs a lemma that the UTF-8 encoding of an ASCII-only `String` is its bytes, which core does not provide |
| Content-Disposition names containing `;` | the proof assumes no `;` (quote-parity grouping then never joins pieces); the property test includes `;` |
| Base64 and quoted-printable decoders | a correctness statement needs an encoder and a model of `binascii`'s non-strict rules; conformance cases mirror every upstream decoder test, properties check them against reference encoders |
| `FormParser` field/file interpretation (CTE, missing name, content type) | it is a pure function of the proved multipart result; conformance cases mirror upstream's |
| Error kinds and offsets | the fixtures in `tests/Fixtures.lean` carry upstream's expected offsets |
| Time and memory on large inputs | `scripts/bench.sh` (in CI) asserts parse time and peak memory (bounds in `tests/Bench.lean`: whole-part parses within 2× Starlette's 455 ms, peak at most three times the body plus the runtime baseline, four for a binary file part) on 50 MB bodies, including the limit cases; `bigChecks` in `tests/Props.lean` covers 2 to 8 MB inputs |

### Deviations from upstream

Each is a `status = "deviation"` row in `docs/traceability.toml`.

1. **Preamble across chunks (UP-001).** Upstream skips a preamble that starts
   with `CR`/`LF` only within one chunk; if the chunk ends inside it, the next
   chunk fails. Here an explicit `preamble` phase persists, so every chunking
   parses.
2. **Header error precedence (UP-006).** Upstream checks the header size of a
   whole chunk span before validating its characters, so the error reported
   for a name that is both oversized and invalid depends on chunking. Here
   each byte is checked for size, then class; both versions reject.
3. **Error offsets.** `MultipartParseError.offset` and
   `QuerystringParseError.offset` are chunk-relative as upstream's;
   `error.offset` is the absolute stream offset, which is what the
   whole-buffer parsers report. A strict-mode "missing `=`" error points at
   the start of the field, as upstream's single-chunk offset does.
4. **Boundary.** A `Boundary` has 1 to 256 bytes (upstream's
   `MAX_BOUNDARY_LENGTH`, not RFC 2046's 70, which upstream does not enforce)
   and only RFC 2046 `bchars`, last byte not a space. Upstream accepts any
   byte; a `CR` in a boundary would break the delimiter search. So
   `MultipartParser.create` raises a `ValueError` for a boundary that is not a
   `Boundary` (`b''` included), where upstream's constructor accepts it and
   fails at the first `write`.
5. **Transfer-encoded parts (UP-002, UP-003).** `FormParser` decodes a
   base64 or quoted-printable part's whole body at once, upstream's
   single-write behaviour, for every chunking. The streaming
   `Base64Decoder` / `QuotedPrintableDecoder` structures reproduce upstream's
   per-write caching exactly.
6. **`FormParser` callbacks** fire at `finalize` (`finalizeWith`), not during
   `write`; the items and their order are upstream's. So with an error in
   the body no callback runs (upstream runs those for the items before it);
   `parseFormStream` inherits this (deviation 10).
7. **Header events** report a header name and value whole when they end;
   upstream may split them at chunk ends. The concatenation is the same.
8. **`max_size < 1`** cannot be configured: the bound is a structure field
   (upstream raises `ValueError`).
9. **Files are held in memory.** `UPLOAD_DIR`, `UPLOAD_KEEP_FILENAME`,
   `UPLOAD_KEEP_EXTENSIONS`, `UPLOAD_DELETE_TMP`, `MAX_MEMORY_FILE_SIZE` and
   the `File` file-object methods are excluded.
10. **`parse_form`** is `parseFormStream headers stream onField onFile
    chunkSize` in `IO`: it reads the stream as upstream does (chunks of
    `chunk_size`, never past `Content-Length`, which is read as Python's
    `int()` reads it, 4300-digit limit included, in one linear pass: `pyInt`) and raises upstream's error classes and messages
    (checked against python-multipart 0.0.32 by the `io:` conformance cases).
    As in deviation 6, the callbacks run once the whole body is read: when the
    body has an error none runs, where upstream calls `on_field` / `on_file`
    for the items before the error and then raises. `parseForm headers body`
    is the pure form over a byte array.
11. **Starlette names** are returned as bytes; decoding with the request
    charset is lean-starlette's job.
12. **`parse_options_header` input is bounded** at `Options.maxLength`
    (16 KiB, as servers bound header blocks): a longer value has no
    parameters. Upstream parses any length; the list-based parser here costs
    tens of bytes per input byte. Multipart part headers are bounded anyway
    by `max_header_size`.

Matching upstream on purpose, though upstream is arguably wrong:
`filename*` and other `*` parameters are ignored (RFC 7578 §4.2); an empty
urlencoded value is `none`, contrary to upstream's docstring (UP-004);
`parse_options_header`'s quote counting is reproduced, including its
mis-split of a quoted value ending in `\\` (UP-005).

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a few
  seconds; `smoke` properties run proved theorems on compiled code, `tested`
  ones cover the table above.
* `tests/Conformance.lean`: cases re-expressed from python-multipart's
  `tests/test_multipart.py` and Starlette's `tests/test_formparsers.py`;
  each names its upstream test. `tests/Fixtures.lean` holds upstream's HTTP
  fixtures (`tests/test_data/http/`) as data.
* `examples/`: the ported upstream examples (`MANIFEST.toml`, checked by
  `stack-tools/check-examples.py`), with `support/` for `hashlib` and `wsgiref`;
  `LeanMultipart/RepoImpl/IOParsers.lean`: the `IO` objects they use.
* `tests/upstream/urlencoded_speed.py`: python-multipart and Starlette's
  `unquote_plus` timings that the `qs-*` bench bounds are 2× of.
* `tests/Bench.lean` with `scripts/bench.sh`: native time and peak-memory
  checks on 50 MB bodies, run in CI.
* `tests/pbt/`: a separate Lake package, the one place an external
  dependency (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol,
theorem and test that realise it. Add a row when behaviour is newly
implemented, tested-only, excluded, or deviates. CI fails if a registered
symbol does not resolve or a test path is missing.

## Upstream defects

Defects found while formalizing are recorded with
`upstream-spec/bin/record-issue` (UP-001 to UP-006 so far) and noted on the
kanban card; see `AGENT-BRIEF.md`.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the library depends on
  Lean core only.
* Choose the definition that suits the automation over a prettier one with
  a harder proof (the printers are written in the shape of the codec
  combinators for this reason).
* No upstream code is copied; the upstream test suite and docs are the spec.
