import Std.Http

/-!
# `wsgiref`, for the examples

python-multipart's documentation runs its examples as WSGI applications
under Python's `wsgiref.simple_server`. Lean has no WSGI, so this helper
gives the part the examples use, on top of `Std.Http`:

* `Environ`: the request's `environ`, read as `environ["CONTENT_TYPE"]!`,
  `environ.contains "CONTENT_LENGTH"` and `environ.wsgiInput`;
* `App`: `simple_app(environ, start_response)`, returning the body pieces;
* `makeServer host port app` and `Server.serveForever`;
* `validator`, which the simple example imports (and does not use);
* `call`, which runs an application on one request in-process, as the
  examples' `curl` sessions do over the network.

It is a helper of the examples, not part of the library.
-/

namespace Wsgiref

/-- The CGI variables of a request, and its body as `wsgi.input`. -/
structure Environ where
  vars : List (String × ByteArray)
  wsgiInput : IO.FS.Stream

/-- `key in environ`. -/
def Environ.contains (e : Environ) (key : String) : Bool := (e.vars.lookup key).isSome

instance : GetElem? Environ String ByteArray (fun e k => e.contains k) where
  getElem e k h := (e.vars.lookup k).get (by simpa [Environ.contains] using h)
  getElem? e k := e.vars.lookup k

/-- WSGI's `start_response(status, response_headers)`. -/
abbrev StartResponse := String → List (String × String) → IO Unit

/-- What an application may return as body pieces: bytes, or (as the
examples, written for Python 2, do) text. -/
class BodyPiece (α : Type) where
  toBytes : α → ByteArray

instance : BodyPiece ByteArray := ⟨id⟩
instance : BodyPiece String := ⟨String.toUTF8⟩

/-- A WSGI application. -/
abbrev App (α : Type) := Environ → StartResponse → IO (List α)

/-- `wsgiref.validate.validator(app)`: here the application itself. -/
def validator {α : Type} (app : App α) : App α := app

/-- Python's `int(...)` on a header value. -/
def int (b : ByteArray) : Nat := ((String.fromUTF8? b).getD "").trimAscii.toString.toNat!

/-- The response of one call: status line, headers, body. -/
structure Reply where
  status : String
  headers : List (String × String)
  body : ByteArray

/-- Run `app` on a request with these CGI variables and body. -/
def call {α : Type} [BodyPiece α] (app : App α) (vars : List (String × ByteArray)) (body : ByteArray) :
    IO Reply := do
  let input ← IO.mkRef ({ data := body } : IO.FS.Stream.Buffer)
  let started ← IO.mkRef ("500 Internal Server Error", ([] : List (String × String)))
  let pieces ← app { vars, wsgiInput := IO.FS.Stream.ofBuffer input } fun st hs => started.set (st, hs)
  let (status, headers) ← started.get
  return { status, headers, body := pieces.foldl (fun acc p => acc ++ BodyPiece.toBytes p) .empty }

/-- A server for one application. -/
structure Server where
  host : String
  port : Nat
  handle : List (String × ByteArray) → ByteArray → IO Reply

/-- `wsgiref.simple_server.make_server(host, port, app)`; `""` is every
interface. -/
def makeServer {α : Type} [BodyPiece α] (host : String) (port : Nat) (app : App α) : IO Server :=
  pure { host, port, handle := call app }

open Std Std.Async Http Server in
/-- `httpd.serve_forever()`. -/
def Server.serveForever (s : Server) : IO Unit := Async.block do
  let addr : Net.SocketAddress := .v4 ⟨if s.host == "" then .ofParts 0 0 0 0 else .ofParts 127 0 0 1, s.port.toUInt16⟩
  let handler : StatelessHandler := {
    onRequest := fun (req : Std.Http.Request Body.Stream) => do
      let mut vars : List (String × ByteArray) := []
      if let some ct := req.line.headers.get? (.mk "content-type") then
        vars := vars ++ [("CONTENT_TYPE", (toString ct).toUTF8)]
      if let some cl := req.line.headers.get? (.mk "content-length") then
        vars := vars ++ [("CONTENT_LENGTH", (toString cl).toUTF8)]
      let body : ByteArray ← req.body.readAll
      let reply ← s.handle vars body
      let code := ((reply.status.splitOn " ").headD "500").toNat!
      let status := (Status.ofCode none code.toUInt16).getD .internalServerError
      let builder := reply.headers.foldl (fun b (k, v) => b.header! k v) (Response.withStatus status)
      let r ← builder.fromBytes reply.body
      return (r : Response Body.Any) }
  let server ← Server.serve addr handler
  server.waitShutdown

end Wsgiref
