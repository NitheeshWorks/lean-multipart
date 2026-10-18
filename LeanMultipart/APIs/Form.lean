import LeanMultipart.Specifications.Multipart
import LeanMultipart.Proofs.Form
import LeanMultipart.APIs.Multipart
import LeanMultipart.Proofs.Unquote
import LeanMultipart.Proofs.Incremental

/-!
# API: forms (upstream's `FormParser`) and Starlette's limited parsers

| Function | Returns |
|---|---|
| `API.parseForm cfg kind body` | `{r // ∀ chunkings, FormParser gives r}` |
| `API.Starlette.parseUrlencoded lim body` | `Except LimitError {fs // Spec.UrlencodedWithinLimits lim fs}` |
| `API.Starlette.parseMultipartForm lim contentType body` | `Except LimitError {ps // Spec.MultipartWithinLimits lim ps}` |
| `API.Starlette.parseUrlencodedForm lim body` | `Except LimitError {items // ∃ fs, Spec.UrlencodedWithinLimits lim fs ∧ items = fs.map decodeField}` |
| `API.Starlette.decodeField f` | Starlette's `unquote_plus(raw.decode("latin-1"))` of a name and value |
| `API.Starlette.parseMultipartChunks lim contentType chunks` | `Except LimitError {ps // Spec.MultipartWithinLimits lim ps ∧ parseMultipartRaw lim contentType (concatChunks chunks) = .ok ps}` |

`Starlette.MultipartStream.create / feed` is the incremental multipart
interface a server drives from its transport (`RepoImpl/Incremental.lean`);
`Starlette.MultipartStream.parseChunks_eq` proves every chunking gives the
whole-buffer parse, and `MultipartStream.feed_retains` that no part data is
kept between chunks.

`FormParser.ofKind / write / finalize` and `createFormParser` are the streaming
interface; `FormParser.write_chunks` proves any chunking equals one write.
-/

namespace LeanMultipart.API

/-- Upstream's `FormParser` over a whole body (`parse_form`): the fields and
files in order, or the first error. The refinement: writing any chunking of
the body to a fresh `FormParser` and finalizing gives the same result. -/
def parseForm (cfg : FormParserConfig) (kind : FormKind) (body : ByteArray)
    (fileName : Option ByteArray := none) :
    {r : Except FormError (List FormItem) //
      ∀ cs : List ByteArray, FormParser.concat cs = body →
        (cs.foldl FormParser.write (FormParser.ofKind cfg kind fileName)).finalize = r} :=
  ⟨parseFormBody cfg kind body fileName, fun cs hcs => by
    rw [FormParser.write_chunks, hcs]; rfl⟩

namespace Starlette

/-- Starlette's `FormParser`: the raw fields of an urlencoded body (names
and values still percent-encoded; `decodeField` decodes them as Starlette
does, and `parseUrlencodedForm` does both), with `max_fields` and `max_part_size` enforced. -/
def parseUrlencoded (lim : FormLimits) (body : ByteArray) :
    Except LimitError {fs : List QsField // Spec.UrlencodedWithinLimits lim fs} :=
  match h : LeanMultipart.Starlette.parseUrlencodedRaw lim body with
  | .error e => .error e
  | .ok fs => .ok ⟨fs, LeanMultipart.Starlette.parseUrlencodedRaw_ok lim body fs h⟩

/-- Starlette's decoding of one raw urlencoded field:
`unquote_plus(name.decode("latin-1"))` and the same for the value
(`unquotePlusLatin1`, compiled to its fast form by `@[csimp]`). -/
def decodeField (f : QsField) : String × String := (unquotePlusLatin1 f.1, unquotePlusLatin1 f.2)

/-- Starlette's `FormParser.parse` on an urlencoded body: the decoded
`(name, value)` pairs, in order, of raw fields within the limits. -/
def parseUrlencodedForm (lim : FormLimits) (body : ByteArray) :
    Except LimitError {items : List (String × String) //
      ∃ fs, Spec.UrlencodedWithinLimits lim fs ∧ items = fs.map decodeField} :=
  (parseUrlencoded lim body).map fun fs => ⟨fs.val.map decodeField, fs.val, fs.property, rfl⟩

/-- Starlette's `MultiPartParser`: the parts of a `multipart/form-data`
body given the request's `Content-Type`, with `max_files`, `max_fields` and
`max_part_size` enforced. -/
def parseMultipartForm (lim : FormLimits) (contentType body : ByteArray) :
    Except LimitError {ps : List StarlettePart // Spec.MultipartWithinLimits lim ps} :=
  match h : LeanMultipart.Starlette.parseMultipartRaw lim contentType body with
  | .error e => .error e
  | .ok ps => .ok ⟨ps, LeanMultipart.Starlette.parseMultipartRaw_ok lim contentType body ps h⟩

/-- Starlette's multipart parse of a body that arrives in chunks, through the
incremental parser. The refinement: the parts are within the limits, and they
are the parts of the whole-buffer parse of the chunks' concatenation. -/
def parseMultipartChunks (lim : FormLimits) (contentType : ByteArray) (chunks : List ByteArray) :
    Except LimitError {ps : List StarlettePart // Spec.MultipartWithinLimits lim ps ∧
      LeanMultipart.Starlette.parseMultipartRaw lim contentType (concatChunks chunks) = .ok ps} :=
  match h : LeanMultipart.Starlette.MultipartStream.parseChunks lim contentType chunks with
  | .error e => .error e
  | .ok ps =>
    have h' : LeanMultipart.Starlette.parseMultipartRaw lim contentType (concatChunks chunks) = .ok ps := by
      rw [← LeanMultipart.Starlette.MultipartStream.parseChunks_eq]; exact h
    .ok ⟨ps, LeanMultipart.Starlette.parseMultipartRaw_ok lim contentType _ ps h', h'⟩

end Starlette
end LeanMultipart.API
