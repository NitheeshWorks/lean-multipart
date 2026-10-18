import LeanMultipart

/-!
# Native time and memory checks

`lake exe bench <case>` builds one input, then times the parse (best of up
to 31 warm runs) and reports
the peak resident memory (`VmHWM` from `/proc/self/status`), which includes
the input itself. `scripts/bench.sh` runs every case in its own process and
fails if a parse takes longer than its bound or the peak exceeds its
multiple of the body plus the runtime's baseline (`bounds`). The reference
is Starlette on the same bodies: 73-109 ms and about 121 MB when a limit
stops a 50 MB body, 455 ms to parse a whole 50 MB file part.
-/

open LeanMultipart

inductive Piece where
  | bytes (b : ByteArray)
  | fill (c : UInt8) (n : Nat)
  | rep (b : ByteArray) (n : Nat)
  /-- `n` pseudo-random bytes (xorshift), so `CR` and partial delimiters occur as in binary files. -/
  | rand (n : Nat)

def Piece.size : Piece → Nat
  | .bytes b => b.size
  | .fill _ n => n
  | .rep b n => b.size * n
  | .rand n => n

/-- Build a body in place, with exact capacity. -/
def build (ps : List Piece) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (ps.foldl (· + ·.size) 0)
  for p in ps do
    match p with
    | .bytes b => out := out ++ b
    | .fill c n => for _ in [0:n] do out := out.push c
    | .rep b n => for _ in [0:n] do out := out ++ b
    | .rand n =>
      let mut x : UInt64 := 88172645463325252
      for _ in [0:n] do
        x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
        out := out.push (x >>> 24).toUInt8
  return out

def mb : Nat := 1024 * 1024
def u (s : String) : ByteArray := s.toUTF8

def bnd : Boundary :=
  match Boundary.ofBytes? "boundary".toUTF8 with
  | some b => b
  | none => ⟨⟨#[98]⟩, by decide⟩

def ctMp : ByteArray := "multipart/form-data; boundary=boundary".toUTF8

def peakKB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for line in s.splitOn "\n" do
    if line.startsWith "VmHWM:" then
      return (String.ofList (line.toList.filter Char.isDigit)).toNat!
  return 0

/-- `a=` and a value of `mib` MiB: plain (`x`), escaped (`%41`), mixed
(`ab+c%20`), spaces as `+` (`hello+world`), or raw UTF-8 (`café`, read as
Latin-1), repeated, as `tests/upstream/urlencoded_speed.py` builds them. -/
def qsValue (kind : String) (mib : Nat) : ByteArray :=
  let unit := match kind with
    | "escaped" => u "%41" | "mixed" => u "ab+c%20" | "plus" => u "hello+world" | "latin" => u "café"
    | _ => u "x"
  let n := mib * mb
  (build [.bytes (u "a="), .rep unit (n / unit.size + 1)]).extract 0 (n + 2)

def qsCases : List (String × String × Nat) :=
  (["plain", "escaped", "mixed"].flatMap fun k => [1, 10, 50].map fun m => (s!"qs-{k}-{m}", k, m)) ++
  (["plus", "latin"].flatMap fun k => [1, 10].map fun m => (s!"qs-{k}-{m}", k, m))

/-- A field name of `mib` MiB of `unit` repeated, then `=1`. -/
def repName (unit : String) (mib : Nat) : ByteArray :=
  let unit := u unit
  (build [.rep unit (mib * mb / unit.size + 1)]).extract 0 (mib * mb) ++ u "=1"

/-- A field name of `mib` MiB of `hello+café` repeated, then `=1`. -/
def plusName (mib : Nat) : ByteArray :=
  let unit := u "hello+café"
  (build [.rep unit (mib * mb / unit.size + 1)]).extract 0 (mib * mb) ++ u "=1"

def body : String → ByteArray
  | "url50" => build [.bytes (u "a="), .fill 120 (50 * mb)]
  | "qsMany" => build [.rep (u "a=b&") 1000000]
  | "mp50" => build [.bytes (u "--boundary\r\nContent-Disposition: form-data; name=\"f\"\r\n\r\n"),
      .fill 120 (50 * mb), .bytes (u "\r\n--boundary--\r\n")]
  | "mpMany" => build [.rep (u "--boundary\r\nContent-Disposition: form-data; name=\"x\"\r\n\r\n\r\n") 1000000,
      .bytes (u "--boundary--\r\n")]
  | "fileBin50" => build [.bytes (u "--boundary\r\nContent-Disposition: form-data; name=\"f\"; filename=\"a\"\r\n\r\n"),
      .rand (50 * mb), .bytes (u "\r\n--boundary--\r\n")]
  | "file50" | "stream50" => build [.bytes (u "--boundary\r\nContent-Disposition: form-data; name=\"f\"; filename=\"a\"\r\n\r\n"),
      .fill 120 (50 * mb), .bytes (u "\r\n--boundary--\r\n")]
  | "percent50" => build [.fill 37 (50 * mb)]
  | "cl1m" => build [.fill 49 mb]
  | "cl10m" => build [.fill 49 (10 * mb)]
  | "cl10mx" => build [.fill 49 (10 * mb), .bytes (u "x")]
  | "options" => build [.bytes (u "text/plain"), .rep (u "; a=b") 2000000]
  | "name-1" => build [.fill 120 mb, .bytes (u "=1")]
  | "name-2" => build [.fill 120 (2 * mb), .bytes (u "=1")]
  | "name-4" => build [.fill 120 (4 * mb), .bytes (u "=1")]
  | "name-over" => build [.fill 120 (mb + 1), .bytes (u "=1")]
  | "name-pw-1" => repName "hello+world" 1
  | "name-pw-2" => repName "hello+world" 2
  | "name-plus-1" => plusName 1
  | "name-plus-10" => plusName 10
  | c => match qsCases.find? (·.1 == c) with
    | some (_, k, m) => qsValue k m
    | none => ByteArray.empty

def run (c : String) (b : ByteArray) : String :=
  match c with
  | "url50" | "qsMany" => match API.Starlette.parseUrlencoded {} b with
    | .error e => s!"{repr e}" | .ok fs => s!"ok {fs.1.length} fields"
  | "mp50" | "mpMany" | "file50" | "fileBin50" => match API.Starlette.parseMultipartForm {} ctMp b with
    | .error e => s!"{repr e}" | .ok ps => s!"ok {ps.1.length} parts"
  | "stream50" => Id.run do
    let chunk := 64 * 1024
    let mut p := MultipartParser.new bnd
    let mut total := 0
    let mut i := 0
    while i < b.size do
      match p.write (b.extract i (i + chunk)) with
      | .ok (p', evs, _) =>
        p := p'
        for e in evs do
          if let .partData d := e then total := total + d.size
      | .error _ => break
      i := i + chunk
    return s!"streamed {total} data bytes"
  | "percent50" => s!"{(percentDecode (percentEncode b)).size == b.size}"
  | "options" => s!"{(parseOptionsHeader b).2.entries.length} params"
  | "qs-plain-1" | "qs-plain-10" | "qs-plain-50" | "qs-escaped-1" | "qs-escaped-10" | "qs-escaped-50"
  | "qs-mixed-1" | "qs-mixed-10" | "qs-mixed-50" | "qs-plus-1" | "qs-plus-10" | "qs-latin-1" | "qs-latin-10" =>
    match API.Starlette.parseUrlencodedForm { maxPartSize := 64 * mb } b with
    | .error e => s!"{repr e}"
    | .ok items => s!"decoded {(items.val.map (·.2.length)).foldl (· + ·) 0} chars"
  | "name-1" | "name-2" | "name-4" | "name-pw-1" | "name-pw-2" | "name-plus-1" | "name-plus-10" =>
    match API.Starlette.parseUrlencodedForm { maxPartSize := 64 * mb } b with
    | .error e => s!"{repr e}"
    | .ok items => s!"decoded {(items.val.map (·.1.length)).foldl (· + ·) 0} name chars"
  | "name-over" => match API.Starlette.parseUrlencodedForm {} b with
    | .error e => s!"{repr e}"
    | .ok _ => "accepted"
  | "cl1m" | "cl10m" | "cl10mx" =>
    match parseForm [("Content-Type", u "application/x-www-form-urlencoded"), ("Content-Length", b)] (u "a=b") with
    | .error e => (toString e).take 60 |>.toString
    | .ok _ => "accepted"
  | c => s!"unknown case {c}"

/-- Per case: the time bound in µs, and the peak-memory bound as a multiple
of the body (plus a 64 MB runtime baseline). The whole-part parses are held
to 2× Starlette's 455 ms. A part with `CR` bytes in it is appended run by
run, and the buffer grows by doubling, so while it grows the peak can reach
three times the part (Starlette spools files to disk instead; files here are
held in memory, a documented deviation). -/
def bounds : String → Nat × Nat
  | "url50" | "mp50" | "qsMany" => (500000, 3)
  | "mpMany" => (1000000, 3)
  | "options" => (100000, 3)
  -- a huge Content-Length is refused in linear time (Python's 4300-digit limit)
  | "cl1m" => (250000, 3)
  -- Starlette's urlencoded parse and decode against python-multipart 0.0.32 +
  -- unquote_plus (tests/upstream/urlencoded_speed.py), held to 2×. Each reference
  -- is the least of three invocations' best of 5 warm runs (best of 15).
  -- Values of 1/10/50 MiB: plain 0.43/7.66/93.0 ms, escaped 102/1068/5298,
  -- mixed 53.4/558/3025; `hello+world` values of 1/10 MiB: 0.96/15.5.
  | "qs-plain-1" => (860, 3) | "qs-plain-10" => (15320, 3) | "qs-plain-50" => (185900, 3)
  | "qs-escaped-1" => (204120, 3) | "qs-escaped-10" => (2136840, 3) | "qs-escaped-50" => (10596000, 3)
  | "qs-mixed-1" => (106800, 3) | "qs-mixed-10" => (1116520, 3) | "qs-mixed-50" => (6049280, 3)
  | "qs-plus-1" => (1920, 3) | "qs-plus-10" => (31000, 3)
  | "cl10m" | "cl10mx" => (1000000, 3)
  -- names: plain `x` of 1/2/4 MiB 0.53/0.87/2.44 ms, `hello+world` of 1/2 MiB
  -- 0.93/1.93; Starlette 1.8.0 refusing a 1 MiB + 1 name at its defaults 0.54
  | "name-1" => (1060, 3) | "name-2" => (1740, 3) | "name-4" => (4880, 3)
  | "name-pw-1" => (1860, 3) | "name-pw-2" => (3860, 3) | "name-over" => (1080, 3)
  -- Raw bytes ≥ 0x80 without `%` (`café` values, `hello+café` names; Python
  -- 0.37/6.52 and 0.87/13.0 ms at 1/10 MiB) are a documented gap
  -- (traceability starlette.decode.nonascii-speed): Python's Latin-1 str is a
  -- copy of the bytes, while each such byte here becomes two UTF-8 bytes,
  -- written one at a time, and the runtime then copies and measures the result
  -- to make the `String`. Held to 2× this port's own time, and to `absCap`.
  | "qs-latin-1" => (6000, 3) | "qs-latin-10" => (70000, 3)
  | "name-plus-1" => (7000, 3) | "name-plus-10" => (70000, 3)
  | "file50" | "stream50" => (910000, 3)
  | "fileBin50" => (910000, 4)
  | "percent50" => (10000000, 8)
  | _ => (0, 0)

/-- Absolute time caps in µs on the rows whose `bounds` are relative to this
port's own time (raw bytes `≥ 0x80`, a documented gap against Python):
1 MiB within 10 ms, 10 MiB within 100 ms, so a regression is caught however
the relative bound was set. -/
def absCap : String → Option Nat
  | "qs-latin-1" | "name-plus-1" => some 10000
  | "qs-latin-10" | "name-plus-10" => some 100000
  | _ => none

def main (args : List String) : IO UInt32 := do
  let some c := args.head? | IO.println "usage: bench <case>"; return 2
  -- Each run gets a freshly built body that it owns, as a server's parser
  -- does; the case name is read back from a ref, so the compiler cannot hoist
  -- the (pure) build and parse out of the loop. The peak memory is read after
  -- the first run. The time is the best of up to 31 runs (fewer once 2 s
  -- have been spent); the Python references are the best of 15
  -- warm runs (three invocations of best of 5).
  let name ← IO.mkRef c
  let mut best := 0
  let mut spent := 0
  let mut outcome := ""
  let mut peak := 0
  let mut size := 0
  for k in [0:31] do
    if k > 0 && spent > 2000000000 then break
    let input := body (← name.get)
    if k == 0 then IO.println s!"{c} built {input.size} bytes"
    size := input.size
    let t0 ← IO.monoNanosNow
    let o := run c input
    if o.length == 0 then IO.println "empty outcome"
    let t1 ← IO.monoNanosNow
    if k == 0 then peak ← peakKB
    if k == 0 || t1 - t0 < best then best := t1 - t0
    spent := spent + (t1 - t0)
    outcome := o
  IO.println s!"{c} outcome={outcome}"
  let us := best / 1000
  IO.println s!"RESULT {c} size={size} ms={us / 1000} us={us} peakKB={peak}"
  let (maxUs, factor) := bounds c
  let maxKB := size * factor / 1024 + 65536
  let mut ok := true
  if us > maxUs then IO.println s!"  FAIL time {us} µs > {maxUs} µs"; ok := false
  if let some cap := absCap c then
    if us > cap then IO.println s!"  FAIL time {us} µs > absolute cap {cap} µs"; ok := false
  if peak > maxKB then IO.println s!"  FAIL memory {peak} KB > {maxKB} KB"; ok := false
  return if ok then 0 else 1
