import LeanMultipart.Specifications.Multipart
import LeanMultipart.Proofs.Wrappers
import LeanMultipart.Proofs.Stream
import LeanMultipart.Proofs.MultipartRoundTrip

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
    refine ⟨fun cs hcs => by rw [MultipartParser.parseChunks_eq, hcs], ?_,
      by rw [Mp.parse_eq]; exact fun e he => (Mp.parse_total ⟨b, cfg⟩ body.data.toList).2 e he⟩
    rw [Mp.parse_eq]
    · have h1 := (Mp.parse_total ⟨b, cfg⟩ body.data.toList).1
      have hr : Mp.room ⟨b, cfg⟩ {} body.data.toList.length ≤ body.data.toList.length := by
        unfold Mp.room; split <;> omega
      have hs : body.size = body.data.toList.length := (Array.length_toList).symm
      rw [hs]; omega⟩

end API
end LeanMultipart

namespace LeanMultipart

instance (cfg : MultipartConfig) (h : ByteArray × ByteArray) : Decidable (Mp.WFHeader cfg h) := by
  unfold Mp.WFHeader; exact inferInstance

instance (cx : Mp.Ctx) (p : RawPart) : Decidable (Mp.WFPart cx p) := by
  unfold Mp.WFPart; exact inferInstance

namespace API

/-- What the multipart printer promises: the parser reads back exactly
these parts, whatever follows (the epilogue). -/
def PrintSpec (cx : Mp.Ctx) (ps : List RawPart) (body : ByteArray) : Prop :=
  ∀ epi : ByteArray, (Mp.parse cx (body ++ epi)).toExcept = .ok ps

instance (cx : Mp.Ctx) (ps : List RawPart) : Decidable (Mp.Fits cx ps) := by
  unfold Mp.Fits
  cases cx.cfg.maxSize with
  | none => exact isTrue (fun m h => by cases h)
  | some m =>
    exact if h : (Mp.printL cx.boundary ps).length ≤ m then isTrue (fun m' h' => by cases h'; exact h)
      else isFalse (fun f => h (f m rfl))

/-- Print a `multipart/form-data` body. Precondition: every part is well
formed (`Mp.WFPart`: no body contains `CR LF -- boundary`; header names
are tokens, values contain no `CR` and do not start with a space; within
the header limits) and the message fits `maxSize`. Postcondition: the
round trip. -/
def printMultipart (cx : Mp.Ctx) (ps : List RawPart) (hw : ∀ p ∈ ps, Mp.WFPart cx p) (hf : Mp.Fits cx ps) :
    {body : ByteArray // PrintSpec cx ps body} :=
  ⟨Mp.print cx.boundary ps, fun epi => Mp.multipart_parse_print_ext cx ps epi hw hf⟩

/-- Why `printMultipart?` refused. -/
inductive PrintError where
  | badPart (index : Nat)
  | tooLarge
  deriving DecidableEq, Repr

/-- `printMultipart` with its precondition checked at runtime. -/
def printMultipart? (cx : Mp.Ctx) (ps : List RawPart) : Except PrintError {body : ByteArray // PrintSpec cx ps body} :=
  if hw : ∀ p ∈ ps, Mp.WFPart cx p then
    if hf : Mp.Fits cx ps then .ok (printMultipart cx ps hw hf) else .error .tooLarge
  else .error (.badPart ((ps.findIdx? (fun p => !decide (Mp.WFPart cx p))).getD 0))

end API
end LeanMultipart
