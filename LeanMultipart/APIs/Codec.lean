import LeanMultipart.Specifications.Codec
import LeanMultipart.Proofs.Wrappers

/-!
# API: percent-encoding and urlencoded forms

Every function takes no precondition and returns its proved postcondition
as a refinement.

| Function | Returns |
|---|---|
| `API.percentEncode b` | `{e // percentDecode e = b}` |
| `API.quotePlus b` | `{e // unquotePlus e = b}` |
| `API.urlencode ps` | `{body // urldecodeB body = ps}` |
| `API.urldecode body` | the pairs (total, non-strict) |
| `API.parseQuerystring cfg body` | `{r // Spec.QsParseSpec cfg body r}` |
-/

namespace LeanMultipart.API

/-- `quote(b, safe="")`, with the decoding round trip. -/
def percentEncode (b : ByteArray) : {e : ByteArray // LeanMultipart.percentDecode e = b} :=
  ⟨LeanMultipart.percentEncode b, percentDecode_percentEncodeB b⟩

/-- `unquote_to_bytes`; total. -/
def percentDecode (b : ByteArray) : ByteArray := LeanMultipart.percentDecode b

/-- `quote_plus(b, safe="")`, with the decoding round trip. -/
def quotePlus (b : ByteArray) : {e : ByteArray // LeanMultipart.unquotePlus e = b} :=
  ⟨LeanMultipart.quotePlus b, unquotePlus_quotePlusB b⟩

/-- `unquote_plus` on bytes; total. -/
def unquotePlus (b : ByteArray) : ByteArray := LeanMultipart.unquotePlus b

/-- `urlencode` on byte pairs: `quote_plus` each, `=` between, `&` between
pairs. The result decodes back to exactly the pairs. -/
def urlencode (ps : List (ByteArray × ByteArray)) : {body : ByteArray // urldecodeB body = ps} :=
  ⟨urlencodeB ps, urldecodeB_urlencodeB ps⟩

/-- Decode an `application/x-www-form-urlencoded` body to pairs, the way
Starlette does at the byte level: non-strict querystring parse, then
`unquote_plus` on every name and value. Total. -/
def urldecode (body : ByteArray) : List (ByteArray × ByteArray) := urldecodeB body

/-- Upstream's `QuerystringParser` over a whole body: the raw fields (still
percent-encoded) or the strict-mode error. The refinement says any chunking
of `body` fed to the streaming parser gives the same result, and an error's
offset lies inside the body. -/
def parseQuerystring (cfg : QsConfig) (body : ByteArray) :
    {r : Except QsError (List QsField) // Spec.QsParseSpec cfg body r} :=
  ⟨Qs.parse cfg body, by
    refine ⟨fun cs hcs => ?_, fun e he => ?_⟩
    · rw [Qs.parse_chunks, hcs]; rfl
    · have ⟨h1, h2⟩ := Qs.parse_total cfg body.data.toList
      have := h2 e he
      have hr : Qs.room cfg {} body.data.toList.length ≤ body.data.toList.length := by
        unfold Qs.room; split <;> omega
      have hs : body.size = body.data.toList.length := (Array.length_toList).symm
      rw [hs]; omega⟩

end LeanMultipart.API
