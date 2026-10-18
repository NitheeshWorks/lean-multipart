import LeanMultipart

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved, plus smoke tests of proved ones (which exercise
the compiled code the proofs are about). Each property names what it checks
and whether it is `tested` (no proof) or a `smoke` test of a theorem.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

open LeanMultipart

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

/-! ## Generators -/

/-- A random list of `n < bound` bytes drawn from `alphabet`. -/
def genFrom (alphabet : Array UInt8) (maxLen : Nat) (r : Rng) : Bytes × Rng := Id.run do
  let (n, r) := r.nat (maxLen + 1)
  let mut r := r
  let mut out : Array UInt8 := #[]
  for _ in [0:n] do
    let (i, r') := r.nat alphabet.size
    r := r'
    out := out.push (alphabet[i]!)
  return (out.toList, r)

def allBytes : Array UInt8 := (List.range 256).toArray.map (·.toUInt8)
def asciiArr (s : String) : Array UInt8 := (ascii s).toArray

/-- Split a list into random chunks. -/
def genChunks (l : Bytes) (r : Rng) : List Bytes × Rng := Id.run do
  let mut r := r
  let mut rest := l
  let mut out : Array Bytes := #[]
  let mut fuel := l.length + 1
  while fuel > 0 do
    fuel := fuel - 1
    if rest.isEmpty then break
    let (k, r') := r.nat (rest.length + 1)
    r := r'
    out := out.push (rest.take k)
    rest := rest.drop k
  out := out.push rest
  return (out.toList, r)

def toBA (l : Bytes) : ByteArray := ⟨l.toArray⟩
def showB (l : Bytes) : String := toString l

/-! ## Event assembly (the consumer side of the callback parsers) -/

/-- Assemble querystring events into fields, as upstream's `FormParser` does. -/
def assembleQs (evs : List QsEvent) : List (Bytes × Bytes) := Id.run do
  let mut out : Array (Bytes × Bytes) := #[]
  let mut n : Bytes := []
  let mut v : Bytes := []
  for e in evs do
    match e with
    | .fieldStart => n := []; v := []
    | .fieldName b => n := n ++ b.data.toList
    | .fieldData b => v := v ++ b.data.toList
    | .fieldEnd => out := out.push (n, v)
    | .end => pure ()
  return out.toList

/-- Run the callback querystring parser over chunks. -/
def runQs (cfg : QsConfig) (chunks : List Bytes) : Except QsError (List QsEvent) := Id.run do
  let mut p : QuerystringParser := { cfg }
  let mut evs : Array QsEvent := #[]
  for c in chunks do
    match p.write (toBA c) with
    | .ok (p', e, _) => p := p'; evs := evs ++ e
    | .error e => return .error e.error
  match p.finalize with
  | .ok e => return .ok (evs ++ e).toList
  | .error e => return .error e

/-- Assemble multipart events into parts. -/
def assembleMp (evs : List MultipartEvent) : List (List (Bytes × Bytes) × Bytes) := Id.run do
  let mut out : Array (List (Bytes × Bytes) × Bytes) := #[]
  let mut hs : Array (Bytes × Bytes) := #[]
  let mut hn : Bytes := []
  let mut hv : Bytes := []
  let mut body : Bytes := []
  for e in evs do
    match e with
    | .partBegin => hs := #[]; body := []
    | .headerBegin => hn := []; hv := []
    | .headerField b => hn := hn ++ b.data.toList
    | .headerValue b => hv := hv ++ b.data.toList
    | .headerEnd => hs := hs.push (hn, hv); hn := []; hv := []
    | .headersFinished => pure ()
    | .partData b => body := body ++ b.data.toList
    | .partEnd => out := out.push (hs.toList, body)
    | .end => pure ()
  return out.toList

def rawView (p : RawPart) : List (Bytes × Bytes) × Bytes :=
  (p.headers.map (fun h => (h.1.data.toList, h.2.data.toList)), p.body.data.toList)

/-- Run the callback multipart parser over chunks. -/
def runMp (b : Boundary) (chunks : List Bytes) : Except MultipartError (List MultipartEvent) := Id.run do
  let mut p := MultipartParser.new b
  let mut evs : Array MultipartEvent := #[]
  for c in chunks do
    match p.write (toBA c) with
    | .ok (p', e, _) => p := p'; evs := evs ++ e
    | .error e => return .error e.error
  return .ok evs.toList

def boundaryB : Boundary :=
  match Boundary.ofBytes? ⟨(ascii "bOuNd-'()+_,./:=?").toArray⟩ with
  | some b => b
  | none => ⟨⟨#[98]⟩, by decide⟩

def shortB : Boundary :=
  match Boundary.ofBytes? ⟨(ascii "b").toArray⟩ with
  | some b => b
  | none => ⟨⟨#[98]⟩, by decide⟩

/-- Random well-formed parts for a boundary: random header names (tokens),
values (no CR, not starting with space), and bodies over a CR/LF/hyphen-heavy
alphabet, rejected if they contain the delimiter. -/
def genParts (b : Boundary) (r : Rng) : List RawPart × Rng := Id.run do
  let (n, r) := r.nat 4
  let mut r := r
  let mut ps : Array RawPart := #[]
  for _ in [0:n] do
    let (nh, r1) := r.nat 4
    r := r1
    let mut hs : Array (ByteArray × ByteArray) := #[]
    for _ in [0:nh] do
      let (hn, r2) := genFrom (asciiArr "abcXYZ-_!#09") 6 r
      let (hv, r3) := genFrom (asciiArr "ab c;=\"\n:\t") 8 r2
      r := r3
      let hn := if hn.isEmpty then ascii "x" else hn
      let hv := hv.dropWhile (· == Byte.SPACE)
      hs := hs.push (toBA hn, toBA hv)
    let (body, r4) := genFrom (#[13, 10, 45, 98, 120] ++ (asciiArr "bOuNd")) 40 r
    r := r4
    let body := if decide (b.delimL <:+: body) then [] else body
    ps := ps.push { headers := hs.toList, body := toBA body }
  return (ps.toList, r)

/-! ## Properties -/

def properties : List Property := [
  { name := "smoke percentDecode_percentEncode (random bytes)"
    check := fun r =>
      let (l, r) := genFrom allBytes 64 r
      let b := toBA l
      (if (percentDecode (percentEncode b)).data.toList == l then none else some (showB l), r) },
  { name := "smoke unquotePlus_quotePlus (random bytes)"
    check := fun r =>
      let (l, r) := genFrom allBytes 64 r
      let b := toBA l
      (if (unquotePlus (quotePlus b)).data.toList == l then none else some (showB l), r) },
  { name := "smoke urldecode_urlencode (random byte pairs)"
    check := fun r => Id.run do
      let (n, r) := r.nat 5
      let mut r := r
      let mut ps : Array (ByteArray × ByteArray) := #[]
      for _ in [0:n] do
        let (a, r1) := genFrom (asciiArr "a &=+%; é") 6 r
        let (b, r2) := genFrom allBytes 6 r1
        r := r2
        ps := ps.push (toBA a, toBA b)
      let back := urldecodeB (urlencodeB ps.toList)
      let ok : Bool := back.length == ps.size && (back.zip ps.toList).all fun (x, y) =>
        x.1.data == y.1.data && x.2.data == y.2.data
      return (bif ok then none else some s!"{ps.toList.map fun p => (p.1.data, p.2.data)}", r) },
  { name := "tested urlencodeStr/urldecodeStr round trip (random Unicode strings)"
    check := fun r => Id.run do
      let chars : Array Char := #['a', ' ', '&', '=', '+', '%', 'é', '中', '🙂', ';']
      let (n, r) := r.nat 4
      let mut r := r
      let mut ps : Array (String × String) := #[]
      for _ in [0:n] do
        let (k, r1) := r.nat 6
        let (v, r2) := r1.nat 6
        let mut s1 := ""
        let mut s2 := ""
        let mut rr := r2
        for _ in [0:k] do
          let (i, r') := rr.nat chars.size; rr := r'; s1 := s1.push chars[i]!
        for _ in [0:v] do
          let (i, r') := rr.nat chars.size; rr := r'; s2 := s2.push chars[i]!
        r := rr
        ps := ps.push (s1, s2)
      let back := urldecodeStr (urlencodeStr ps.toList)
      return (if back == ps.toList then none else some s!"{ps}", r) },
  { name := "smoke QuerystringParser.parseChunks_eq: events = whole-buffer fields (random bodies, random chunking)"
    check := fun r => Id.run do
      let (body, r) := genFrom (asciiArr "ab=&;%+") 30 r
      let (chunks, r) := genChunks body r
      let whole := Qs.parse {} (toBA body)
      let ok : Bool := match whole, runQs {} chunks with
        | .ok fs, .ok evs => assembleQs evs == fs.map (fun f => (f.1.data.toList, f.2.data.toList))
        | _, _ => false
      return (bif ok then none else some s!"{showB body} chunks {chunks}", r) },
  { name := "smoke QuerystringParser.parseChunks_eq: strict errors = whole-buffer errors (random chunking)"
    check := fun r => Id.run do
      let (body, r) := genFrom (asciiArr "ab=&") 20 r
      let (chunks, r) := genChunks body r
      let cfg : QsConfig := { strictParsing := true }
      let ok : Bool := match Qs.parse cfg (toBA body), runQs cfg chunks with
        | .ok fs, .ok evs => assembleQs evs == fs.map (fun f => (f.1.data.toList, f.2.data.toList))
        | .error e1, .error e2 => e1 == e2
        | _, _ => false
      return (bif ok then none else some s!"{showB body} chunks {chunks}", r) },
  { name := "smoke multipart_parse_print_ext (random parts and epilogue)"
    check := fun r => Id.run do
      let (ps, r) := genParts boundaryB r
      let (epi, r) := genFrom allBytes 20 r
      let body := Mp.print boundaryB ps ++ toBA epi
      let res := Mp.parse { boundary := boundaryB } body
      let ok : Bool := res.ended && res.error.isNone && res.parts.map rawView == ps.map rawView
      return (bif ok then none else some s!"{ps.map rawView}", r) },
  { name := "smoke MultipartParser.parseChunks_eq: events = whole-buffer parts (printed messages, random chunking)"
    check := fun r => Id.run do
      let (ps, r) := genParts shortB r
      let body := (Mp.print shortB ps).data.toList
      let (chunks, r) := genChunks body r
      let whole := Mp.parse { boundary := shortB } (toBA body)
      let ok : Bool := match runMp shortB chunks with
        | .ok evs => assembleMp evs == whole.parts.map rawView
        | .error _ => false
      return (bif ok then none else some s!"{showB body} chunks {chunks}", r) },
  { name := "smoke MultipartParser.parseChunks_eq: events = whole-buffer parts (fuzzed messages, random chunking)"
    check := fun r => Id.run do
      let (ps, r) := genParts shortB r
      let body := (Mp.print shortB ps).data.toList
      -- mutate: insert, delete or swap one byte
      let (op, r) := r.nat 3
      let (i, r) := r.nat (body.length + 1)
      let (c, r) := r.nat 256
      let body := match op with
        | 0 => body.take i ++ [c.toUInt8] ++ body.drop i
        | 1 => body.take i ++ body.drop (i + 1)
        | _ => body.take i ++ (body.drop i).take 2 |>.reverse |> (· ++ body.drop (i + 2))
      let (chunks, r) := genChunks body r
      let whole := Mp.parse { boundary := shortB } (toBA body)
      let ok : Bool := match runMp shortB chunks, whole.error with
        | .ok evs, none => assembleMp evs == whole.parts.map rawView
        | .error e, some e' => e == e'
        | _, _ => false
      return (bif ok then none else some s!"{showB body} chunks {chunks}", r) },
  { name := "smoke dispositionParams_formPart, and tested with `;` in names"
    check := fun r => Id.run do
      let alpha := asciiArr "aZ09 _-.()=,é:/;"
      let (n, r) := genFrom alpha 10 r
      let (f, r) := genFrom alpha 10 r
      let (hasFile, r) := r.nat 2
      let fn := if hasFile == 1 then some (toBA f) else none
      let part := formPart (toBA n) fn none ByteArray.empty
      let (n', f') := dispositionParams part.headers
      let ok : Bool := n' == some n && f' == (if hasFile == 1 then some f else none)
      return (bif ok then none else some s!"{showB n} {showB f}", r) },
  { name := "smoke FormParser chunking (urlencoded and multipart)"
    check := fun r => Id.run do
      let (ps, r) := genParts shortB r
      let body := (Mp.print shortB ps).data.toList
      let (chunks, r) := genChunks body r
      let p := FormParser.ofKind {} (.multipart shortB)
      let a := (chunks.foldl (fun p c => p.write (toBA c)) p).finalize
      let b := (p.write (toBA body)).finalize
      let same := match a, b with
        | .ok x, .ok y => x.length == y.length
        | .error _, .error _ => true
        | _, _ => false
      return (bif same then none else some (showB body), r) },
  { name := "smoke Starlette limits hold of accepted forms"
    check := fun r => Id.run do
      let (n, r) := r.nat 6
      let lim : FormLimits := { maxFields := 3, maxFiles := 2, maxPartSize := 5 }
      let mut ps : Array RawPart := #[]
      let mut r := r
      for i in [0:n] do
        let (isFile, r1) := r.nat 2
        let (len, r2) := r1.nat 8
        r := r2
        ps := ps.push (formPart (toBA (ascii s!"f{i}")) (if isFile == 1 then some (toBA (ascii "x")) else none)
          none (toBA (List.replicate len 97)))
      let body := Mp.print shortB ps.toList
      let res := API.Starlette.parseMultipartForm lim (toBA (ascii "multipart/form-data; boundary=b")) body
      let ok : Bool := match res with
        | .ok sp => decide ((sp.1.filter (·.isFile)).length ≤ 2) && decide ((sp.1.filter (!·.isFile)).length ≤ 3) &&
            sp.1.all (fun p => p.isFile || decide (p.data.size ≤ 5))
        | .error _ => true
      return (bif ok then none else some s!"{n}", r) },
  { name := "tested base64 decoder inverts standard encoding (random bytes)"
    check := fun r => Id.run do
      let (l, r) := genFrom allBytes 40 r
      let tbl := asciiArr "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
      let arr := l.toArray
      let mut out : Array UInt8 := #[]
      let mut i := 0
      while i + 3 ≤ arr.size do
        let n := arr[i]!.toNat * 65536 + arr[i+1]!.toNat * 256 + arr[i+2]!.toNat
        out := out ++ #[tbl[n / 262144 % 64]!, tbl[n / 4096 % 64]!, tbl[n / 64 % 64]!, tbl[n % 64]!]
        i := i + 3
      if arr.size - i == 1 then
        let n := arr[i]!.toNat * 65536
        out := out ++ #[tbl[n / 262144 % 64]!, tbl[n / 4096 % 64]!, 61, 61]
      else if arr.size - i == 2 then
        let n := arr[i]!.toNat * 65536 + arr[i+1]!.toNat * 256
        out := out ++ #[tbl[n / 262144 % 64]!, tbl[n / 4096 % 64]!, tbl[n / 64 % 64]!, 61]
      let ok : Bool := match decodeBase64 ⟨out⟩ with
        | .ok d => d.data.toList == l
        | .error _ => false
      return (bif ok then none else some (showB l), r) },
  { name := "tested quoted-printable decoder inverts =XX encoding with soft line breaks"
    check := fun r => Id.run do
      let (l, r) := genFrom allBytes 30 r
      let hex := asciiArr "0123456789ABCDEF"
      let mut enc : Array UInt8 := #[]
      let mut col := 0
      for c in l do
        if col ≥ 20 then
          enc := enc ++ #[61, 13, 10]; col := 0
        if (Byte.isAlpha c || Byte.isDigit c) then enc := enc.push c; col := col + 1
        else enc := enc ++ #[61, hex[c.toNat / 16]!, hex[c.toNat % 16]!]; col := col + 3
      let ok : Bool := (decodeQuotedPrintable ⟨enc⟩).data.toList == l
      return (bif ok then none else some (showB l), r) }
]

/-- Linear-time checks on large inputs (review finding: quadratic streaming
and stack overflow). They print their timing; a regression shows up as a
timeout in CI rather than a flaky threshold here. -/
def bigChecks : IO Bool := do
  let n := 2000000
  let body : ByteArray := ⟨(ascii "a=").toArray ++ Array.replicate n 98⟩
  let t0 ← IO.monoMsNow
  let ok1 := match (QuerystringParser.new).write body with
    | .ok (p, evs, k) => k == body.size && (match p.finalize with | .ok _ => true | .error _ => false) && evs.size ≥ 2
    | .error _ => false
  let t1 ← IO.monoMsNow
  let big : ByteArray := ⟨Array.replicate (4 * n) 37⟩
  let ok2 := (percentDecode (percentEncode big)).size == big.size
  let t2 ← IO.monoMsNow
  let mpBody := Mp.print shortB [{ headers := [], body := ⟨Array.replicate (4 * n) 120⟩ }]
  let ok3 := match (MultipartParser.new shortB).write mpBody with
    | .ok (_, evs, _) => evs.size ≥ 3
    | .error _ => false
  let t3 ← IO.monoMsNow
  IO.println s!"big    QuerystringParser 2 MB value {t1 - t0} ms, percent codec 8 MB {t2 - t1} ms, MultipartParser 8 MB part {t3 - t2} ms"
  return ok1 && ok2 && ok3

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  let big ← bigChecks
  unless big do
    failures := failures + 1
    IO.println "FAIL  big inputs"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
