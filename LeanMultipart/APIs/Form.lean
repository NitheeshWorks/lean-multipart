import LeanMultipart.Specifications.Multipart
import LeanMultipart.Proofs.Form
import LeanMultipart.APIs.Multipart

/-!
# API: forms (upstream's `FormParser`) and Starlette's limited parsers

| Function | Returns |
|---|---|
| `API.parseForm cfg kind body` | `{r // ∀ chunkings, FormParser gives r}` |
| `API.Starlette.parseUrlencoded lim body` | `Except LimitError {fs // Spec.UrlencodedWithinLimits lim fs}` |
| `API.Starlette.parseMultipartForm lim contentType body` | `Except LimitError {ps // Spec.MultipartWithinLimits lim ps}` |

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
and values still percent-encoded; decode with `API.unquotePlus` and the
request charset), with `max_fields` and `max_part_size` enforced. -/
def parseUrlencoded (lim : FormLimits) (body : ByteArray) :
    Except LimitError {fs : List QsField // Spec.UrlencodedWithinLimits lim fs} :=
  match h : LeanMultipart.Starlette.parseUrlencodedRaw lim body with
  | .error e => .error e
  | .ok fs => .ok ⟨fs, LeanMultipart.Starlette.parseUrlencodedRaw_ok lim body fs h⟩

/-- Starlette's `MultiPartParser`: the parts of a `multipart/form-data`
body given the request's `Content-Type`, with `max_files`, `max_fields` and
`max_part_size` enforced. -/
def parseMultipartForm (lim : FormLimits) (contentType body : ByteArray) :
    Except LimitError {ps : List StarlettePart // Spec.MultipartWithinLimits lim ps} :=
  match h : LeanMultipart.Starlette.parseMultipartRaw lim contentType body with
  | .error e => .error e
  | .ok ps => .ok ⟨ps, LeanMultipart.Starlette.parseMultipartRaw_ok lim contentType body ps h⟩

end Starlette
end LeanMultipart.API
