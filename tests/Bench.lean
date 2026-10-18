import LeanMultipart

/-!
# Native time and memory checks

`lake exe bench <case>` builds one input, then times the parse and reports
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
  | _ => ByteArray.empty

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
  | "cl1m" | "cl10m" | "cl10mx" =>
    match parseForm [("Content-Type", u "application/x-www-form-urlencoded"), ("Content-Length", b)] (u "a=b") with
    | .error e => (toString e).take 60 |>.toString
    | .ok _ => "accepted"
  | c => s!"unknown case {c}"

/-- Per case: the time bound in ms, and the peak-memory bound as a multiple
of the body (plus a 64 MB runtime baseline). The whole-part parses are held
to 2× Starlette's 455 ms. A part with `CR` bytes in it is appended run by
run, and the buffer grows by doubling, so while it grows the peak can reach
three times the part (Starlette spools files to disk instead; files here are
held in memory, a documented deviation). -/
def bounds : String → Nat × Nat
  | "url50" | "mp50" | "qsMany" => (500, 3)
  | "mpMany" => (1000, 3)
  | "options" => (100, 3)
  -- a huge Content-Length is refused in linear time (Python's 4300-digit limit)
  | "cl1m" => (250, 3)
  | "cl10m" | "cl10mx" => (1000, 3)
  | "file50" | "stream50" => (910, 3)
  | "fileBin50" => (910, 4)
  | "percent50" => (10000, 8)
  | _ => (0, 0)

def main (args : List String) : IO UInt32 := do
  let some c := args.head? | IO.println "usage: bench <case>"; return 2
  let b := body c
  IO.println s!"{c} built {b.size} bytes"
  let t0 ← IO.monoMsNow
  let outcome := run c b
  IO.println s!"{c} outcome={outcome}"
  let t1 ← IO.monoMsNow
  let peak ← peakKB
  IO.println s!"RESULT {c} size={b.size} ms={t1 - t0} peakKB={peak}"
  let (maxMs, factor) := bounds c
  let maxKB := b.size * factor / 1024 + 65536
  let mut ok := true
  if t1 - t0 > maxMs then IO.println s!"  FAIL time {t1 - t0} ms > {maxMs} ms"; ok := false
  if peak > maxKB then IO.println s!"  FAIL memory {peak} KB > {maxKB} KB"; ok := false
  return if ok then 0 else 1
