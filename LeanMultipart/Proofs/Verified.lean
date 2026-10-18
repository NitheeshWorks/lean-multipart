import LeanMultipart.Proofs.Percent
import LeanMultipart.Proofs.Querystring
import LeanMultipart.Proofs.MultipartRoundTrip
import LeanMultipart.Proofs.Stream
import LeanMultipart.Proofs.Form
import LeanMultipart.Proofs.Incremental
import LeanMultipart.Proofs.Wrappers
import LeanMultipart.Proofs.Options
import LeanMultipart.Specifications
import LeanMultipart.APIs

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a layer's implementation with a proof term for
every `Specifications/<Layer>.lean` property it claims. A specification with
no proof is a compile error the moment it needs a field here: you cannot
construct a `Verified<Layer>` value without every proof in hand. What is
tested rather than proved has no field; it is listed in `CONTRIBUTING.md`
and in `docs/traceability.toml` with `status = "tested"`.
-/

namespace LeanMultipart

/-- Percent-encoding: `unquote_to_bytes` undoes `quote`, and `unquote_plus`
undoes `quote_plus`, on any continuation of the buffer. -/
structure VerifiedPercent where
  percentRoundTrip : Spec.PercentRoundTrip
  quotePlusRoundTrip : Spec.QuotePlusRoundTrip

theorem theVerifiedPercent : VerifiedPercent where
  percentRoundTrip := percentDecode_percentEncode_extB
  quotePlusRoundTrip := unquotePlus_quotePlus_extB

/-- `application/x-www-form-urlencoded`: the round trip (plain and `_ext`),
the streaming `QuerystringParser` gives the whole-buffer result for every
split of the input, and totality with error localisation. -/
structure VerifiedUrlencoded where
  roundTrip : Spec.UrlencodeRoundTrip
  roundTripExt : Spec.UrlencodeRoundTripExt
  streaming : ∀ cfg, Spec.QsStreamingAgrees cfg
  total : ∀ cfg, Spec.QsTotal cfg

theorem theVerifiedUrlencoded : VerifiedUrlencoded where
  roundTrip := urldecodeB_urlencodeB
  roundTripExt := urldecodeB_urlencodeB_ext
  streaming := QuerystringParser.parseChunks_eq
  total := Qs.parse_total

/-- `multipart/form-data`: the round trip on any epilogue, the streaming
`MultipartParser` gives the whole-buffer parts for every split of the
input, totality, and a parsed boundary satisfies its refinement. -/
structure VerifiedMultipart where
  roundTrip : ∀ cx, Spec.MultipartRoundTrip cx
  streaming : ∀ cx, Spec.MpStreamingAgrees cx
  total : ∀ cx, Spec.MpTotal cx
  boundaryValid : ∀ ct b, API.parseBoundary ct = .ok b → ValidBoundary b.1

theorem theVerifiedMultipart : VerifiedMultipart where
  roundTrip := fun cx ps epi hw hf => Mp.multipart_parse_print_ext cx ps epi hw hf
  streaming := MultipartParser.parseChunks_eq
  total := Mp.parse_total
  boundaryValid := API.parseBoundary_valid

/-- Forms: `FormParser` fed any chunking equals one write, the
`Content-Disposition` a part is printed with is read back, Starlette's
limits hold of every accepted form, and Starlette's incremental multipart
parser gives the whole-buffer result for every chunking while keeping no
part data between chunks. -/
structure VerifiedForm where
  streaming : Spec.FormStreamingAgrees
  dispositionRoundTrip : Spec.DispositionRoundTrip
  urlencodedLimits : ∀ lim body fs, Starlette.parseUrlencodedRaw lim body = .ok fs →
    Spec.UrlencodedWithinLimits lim fs
  multipartLimits : ∀ lim ct body ps, Starlette.parseMultipartRaw lim ct body = .ok ps →
    Spec.MultipartWithinLimits lim ps
  starletteStreaming : Spec.StarletteStreamingAgrees
  starletteBounded : Spec.StarletteBounded
  incremental : Spec.IncrementalAgrees
  incrementalRetains : Spec.IncrementalRetains

theorem theVerifiedForm : VerifiedForm where
  streaming := FormParser.write_chunks
  dispositionRoundTrip := dispositionParams_formPart
  urlencodedLimits := Starlette.parseUrlencodedRaw_ok
  multipartLimits := Starlette.parseMultipartRaw_ok
  starletteStreaming := ⟨Starlette.UrlencodedParser.finalize_chunks, Starlette.MultipartFormParser.finalize_chunks⟩
  starletteBounded := ⟨Starlette.urlencoded_bounded, Starlette.multipart_bounded⟩
  incremental := Starlette.MultipartStream.parseChunks_eq
  incrementalRetains := ⟨Starlette.new_retained, Starlette.MultipartStream.feed_retains⟩

end LeanMultipart
