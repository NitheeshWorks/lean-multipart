import LeanMultipart.Specifications.Multipart
import LeanMultipart.Proofs.Wrappers

/-!
# API: multipart/form-data

| Function | Returns |
|---|---|
| `API.parseBoundary contentType` | `Except BoundaryError {b // ValidBoundary b}` |
| `API.boundary contentType` | `Except BoundaryError Boundary` |
| `API.parseMultipart b cfg body` | `{r // Spec.MpParseSpec ⟨b, cfg⟩ body r}` |
| `MultipartParser.new / write / finalize` | the streaming, callback-style parser |
-/

namespace LeanMultipart

/-- Why a `Content-Type` gave no boundary. -/
inductive BoundaryError where
  /-- No `boundary` parameter (Starlette: "Missing boundary in multipart."). -/
  | missing
  /-- The parameter is not a valid boundary (empty, longer than 256 bytes,
  or a byte outside RFC 2046 `bchars`). -/
  | invalid
  deriving DecidableEq, Repr, Inhabited

namespace API

/-- The `boundary` parameter of a `Content-Type` header value, parsed as
upstream's `parse_options_header` does, and checked: the result satisfies
the boundary refinement. -/
def parseBoundary (contentType : ByteArray) : Except BoundaryError {b : ByteArray // ValidBoundary b} :=
  match Starlette.boundaryParam contentType with
  | none => .error .missing
  | some b =>
    let bs : ByteArray := ⟨b.toArray⟩
    if h : ValidBoundary bs then .ok ⟨bs, h⟩ else .error .invalid

/-- `parseBoundary`, as a `Boundary`. -/
def boundary (contentType : ByteArray) : Except BoundaryError Boundary :=
  (parseBoundary contentType).map fun b => ⟨b.1, b.2⟩

/-- A parsed boundary satisfies its refinement (by construction). -/
theorem parseBoundary_valid (ct : ByteArray) (b : {b : ByteArray // ValidBoundary b})
    (_h : parseBoundary ct = .ok b) : ValidBoundary b.1 := b.2

/-- Upstream's `MultipartParser` over a whole body: completed parts, the
part in progress, whether the closing delimiter was seen, the first error,
and the bytes processed. The refinement: any chunking fed to the streaming
parser gives the same result, at most the body is processed, and an error's
offset lies in the processed bytes. -/
def parseMultipart (b : Boundary) (cfg : MultipartConfig) (body : ByteArray) :
    {r : MultipartResult // Spec.MpParseSpec ⟨b, cfg⟩ body r} :=
  ⟨Mp.parse ⟨b, cfg⟩ body, by
    refine ⟨fun cs hcs => ?_, ?_, fun e he => (Mp.parse_total ⟨b, cfg⟩ body.data.toList).2 e he⟩
    · rw [Mp.parse_chunks, hcs]; rfl
    · have h1 := (Mp.parse_total ⟨b, cfg⟩ body.data.toList).1
      have hr : Mp.room ⟨b, cfg⟩ {} body.data.toList.length ≤ body.data.toList.length := by
        unfold Mp.room; split <;> omega
      have hs : body.size = body.data.toList.length := (Array.length_toList).symm
      simp only [Mp.parse] at h1 ⊢
      rw [hs]; omega⟩

end API
end LeanMultipart
