import LeanMultipart
import examples.support.Hashlib
import examples.support.Wsgiref

/-!
# docs/index.md

A port of the Python code blocks of python-multipart's `docs/index.md`
("Quickstart"), in order:

1. "Simple Example": `parse_form` in a WSGI application (`SimpleExample`);
2. "In-Depth Example", the starting application (`InDepthStart`);
3. "In-Depth Example", the final code: a `MultipartParser` hashing each
   part with SHA-256 as it streams (`InDepth`).

Python's `wsgiref` and `hashlib` are stood in for by `examples/support/`.
`lake exe docs-index serve simple|start|in-depth` serves a block on port
8123 as upstream does; `lake exe docs-index` replays the page's `curl`
sessions in-process and prints each response, which
`tests/Conformance.lean` compares with upstream's output.
-/

open LeanMultipart Wsgiref

namespace SimpleExample

def simpleApp (environ : Environ) (startResponse : StartResponse) : IO (List ByteArray) := do
  let ret ← IO.mkRef (#[] : Array ByteArray)

  -- The following two callbacks just append the name to the return value.
  let onField (field : Field) :=
    ret.modify (·.push ("Parsed value parameter named: ".toUTF8 ++ field.fieldName))

  let onFile (file : File) :=
    ret.modify (·.push ("Parsed file parameter named: ".toUTF8 ++ file.fieldName.getD .empty))

  -- Create headers object.  We need to convert from WSGI to the actual
  -- name of the header, since this library does not assume that you are
  -- using WSGI.
  let mut headers : Headers := [("Content-Type", environ["CONTENT_TYPE"]!)]
  if environ.contains "CONTENT_LENGTH" then
    headers := headers ++ [("Content-Length", environ["CONTENT_LENGTH"]!)]

  -- Parse the form.
  parseFormStream headers environ.wsgiInput onField onFile

  -- Return something.
  startResponse "200 OK" [("Content-type", "text/plain")]
  ret.modify (·.push "\n".toUTF8)
  return (← ret.get).toList

def serve : IO Unit := do
  let _ := validator simpleApp
  let httpd ← makeServer "" 8123 simpleApp
  IO.println "Serving on port 8123..."
  httpd.serveForever

end SimpleExample

namespace InDepthStart

def simpleApp (_environ : Environ) (startResponse : StartResponse) : IO (List String) := do
  startResponse "200 OK" [("Content-type", "text/plain")]
  return ["Hashes:\n"]

def serve : IO Unit := do
  let httpd ← makeServer "" 8123 simpleApp
  IO.println "Serving on port 8123..."
  httpd.serveForever

end InDepthStart

namespace InDepth

def simpleApp (environ : Environ) (startResponse : StartResponse) : IO (List String) := do
  let ret ← IO.mkRef (#[] : Array String)

  -- The hash of the current part, in a mutable reference the callbacks
  -- share (upstream's Python 2 code uses a class attribute for this).
  let hash ← IO.mkRef Hashlib.sha256

  -- This is called when a new part arrives.  We create a new hash object
  -- in this callback.
  let onPartBegin := hash.set Hashlib.sha256

  -- We got some data!  Update our hash.
  let onPartData (data : ByteArray) := hash.modify (·.update data)

  -- Our current part is done, so we can finish the hash.
  let onPartEnd := do ret.modify (·.push s!"Part hash: {(← hash.get).hexdigest}")

  -- Parse the Content-Type header to get the multipart boundary.
  let (_contentType, params) := parseOptionsHeader environ["CONTENT_TYPE"]!
  let boundary := params.get "boundary"

  -- Callbacks dictionary.
  let callbacks : MultipartCallbacks IO := { onPartBegin, onPartData, onPartEnd }

  -- Create the parser.
  let parser ← MultipartParser.create boundary callbacks

  -- The input stream is from the WSGI environ.
  let inp := environ.wsgiInput

  -- Feed the parser with data from the request.
  let mut size := int environ["CONTENT_LENGTH"]!
  while size > 0 do
    let toRead := min size (1024 * 1024)
    let data ← inp.read toRead.toUSize
    discard <| parser.write data

    size := size - data.size
    if data.size != toRead then
      break

  startResponse "200 OK" [("Content-type", "text/plain")]
  return (← ret.get).toList

def serve : IO Unit := do
  let httpd ← makeServer "" 8123 simpleApp
  IO.println "Serving on port 8123..."
  httpd.serveForever

end InDepth

/-! ## The page's `curl` sessions -/

/-- The body `curl -F` sends, with curl's boundary style. -/
def curlForm (boundary : String) (parts : List String) : List (String × ByteArray) × ByteArray :=
  let body := String.join (parts.map (s!"--{boundary}\r\n" ++ ·)) ++ s!"--{boundary}--\r\n"
  ([("CONTENT_TYPE", s!"multipart/form-data; boundary={boundary}".toUTF8),
    ("CONTENT_LENGTH", (toString body.utf8ByteSize).toUTF8)], body.toUTF8)

def printReply (title : String) (r : Reply) : IO Unit := do
  IO.println s!"== {title} =="
  IO.println r.status
  for (k, v) in r.headers do IO.println s!"{k}: {v}"
  IO.println ""
  (← IO.getStdout).write r.body
  IO.println ""

def main (args : List String) : IO Unit := do
  match args with
  | ["serve", "simple"] => SimpleExample.serve
  | ["serve", "start"] => InDepthStart.serve
  | ["serve", "in-depth"] => InDepth.serve
  | _ =>
    -- curl -ik -F "foo=bar" http://localhost:8123/
    let (vars, body) := curlForm "------------------------c2ef3ebd0a8a1a63"
      ["Content-Disposition: form-data; name=\"foo\"\r\n\r\nbar\r\n"]
    printReply "simple: curl -F foo=bar" (← call SimpleExample.simpleApp vars body)
    -- curl -ik http://localhost:8123/
    printReply "in-depth start: curl" (← call InDepthStart.simpleApp [] .empty)
    -- curl -ik -F file=@/tmp/test.txt http://localhost:8123/   (test.txt is "Foo bar\n")
    let (vars, body) := curlForm "------------------------8f2c63b9d2c1e7a4"
      ["Content-Disposition: form-data; name=\"file\"; filename=\"test.txt\"\r\nContent-Type: text/plain\r\n\r\nFoo bar\n\r\n"]
    printReply "in-depth: curl -F file=@/tmp/test.txt" (← call InDepth.simpleApp vars body)
