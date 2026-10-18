import LeanMultipart

/-!
# The python-multipart quickstart, in Lean

The two examples from upstream's documentation (`docs/index.md`,
"Quickstart"), translated. The README shows the same code; this file keeps
it compiling, and `main` runs it on a sample body.
-/

open LeanMultipart

/-- Upstream's "Simple Example": `parse_form` with `on_field` / `on_file`
callbacks that report each parameter's name. -/
def simpleApp (contentType body : ByteArray) : Except FormError (List String) := do
  let items ← parseForm [("Content-Type", contentType)] body
  return items.map fun
    | .field f => s!"Parsed value parameter named: {latin1Decode f.fieldName}"
    | .file f => s!"Parsed file parameter named: {(f.fieldName.map latin1Decode).getD ""}"

/-- The same, with callbacks, in any monad (here `StateM` collecting lines). -/
def simpleAppWith (contentType body : ByteArray) : StateM (Array String) (Except FormError Unit) :=
  parseFormWith [("Content-Type", contentType)] body
    (onField := fun f => modify (·.push s!"Parsed value parameter named: {latin1Decode f.fieldName}"))
    (onFile := fun f => modify (·.push s!"Parsed file parameter named: {(f.fieldName.map latin1Decode).getD ""}"))

/-- Upstream's "In-Depth Example": a `MultipartParser` with `on_part_begin`
/ `on_part_data` / `on_part_end` callbacks, fed the body chunk by chunk, so
no part is held in memory. Upstream hashes each part with SHA-256; this
library has no hash function, so the example sums each part's bytes. -/
def partChecksums (contentType : ByteArray) (chunks : List ByteArray) : Except String (List Nat) := do
  let (_, params) := parseOptionsHeader contentType
  let some b := params.get "boundary" | throw "no boundary"
  let some boundary := Boundary.ofBytes? b | throw "invalid boundary"
  let mut parser := MultipartParser.new boundary
  let mut sums : Array Nat := #[]
  let mut current := 0
  for chunk in chunks do
    match parser.write chunk with
    | .error e => throw s!"parse error at offset {e.offset}"
    | .ok (p, events, _) =>
      parser := p
      for ev in events do
        match ev with
        | .partBegin => current := 0
        | .partData d => current := d.foldl (fun acc x => acc + x.toNat) current
        | .partEnd => sums := sums.push current
        | _ => pure ()
  return sums.toList

def sampleBody : ByteArray :=
  ("--boundary\r\nContent-Disposition: form-data; name=\"foo\"\r\n\r\nbar\r\n" ++
   "--boundary\r\nContent-Disposition: form-data; name=\"file\"; filename=\"a.txt\"\r\n" ++
   "Content-Type: text/plain\r\n\r\nhello\r\n--boundary--\r\n").toUTF8

def main : IO Unit := do
  let ct := "multipart/form-data; boundary=boundary".toUTF8
  IO.println (repr (simpleApp ct sampleBody |>.toOption))
  IO.println (repr ((simpleAppWith ct sampleBody).run #[]).2)
  -- feed the body in 7-byte chunks
  let chunks := (List.range ((sampleBody.size + 6) / 7)).map fun i => sampleBody.extract (7 * i) (7 * i + 7)
  IO.println (repr (partChecksums ct chunks |>.toOption))
