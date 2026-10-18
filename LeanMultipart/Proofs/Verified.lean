import LeanMultipart.Proofs.Percent
import LeanMultipart.Proofs.Querystring
import LeanMultipart.Proofs.MultipartRoundTrip
import LeanMultipart.Proofs.Stream
import LeanMultipart.Proofs.Form
import LeanMultipart.Proofs.Wrappers
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

/-- Percent-encoding: `quote` / `unquote_to_bytes` and `quote_plus` /
`unquote_plus` round-trip on any continuation, and the stack-safe forms
the API runs equal the list specifications. -/
structure VerifiedPercent where
  percentRoundTrip : Spec.PercentRoundTrip percentEncodeL percentDecodeL
  quotePlusRoundTrip : Spec.PercentRoundTrip quotePlusL unquotePlusL
  encodeTR : ∀ b : ByteArray, (percentEncode b).data.toList = percentEncodeL b.data.toList
  decodeTR : ∀ b : ByteArray, (percentDecode b).data.toList = percentDecodeL b.data.toList
  bytesRoundTrip : ∀ b : ByteArray, percentDecode (percentEncode b) = b

theorem theVerifiedPercent : VerifiedPercent where
  percentRoundTrip := percentDecode_percentEncode_ext
  quotePlusRoundTrip := unquotePlus_quotePlus_ext
  encodeTR := percentEncode_toList
  decodeTR := percentDecode_toList
  bytesRoundTrip := percentDecode_percentEncodeB

/-- `application/x-www-form-urlencoded`: the round trip (plain and `_ext`),
the streaming `QuerystringParser` gives the whole-buffer result for every
split of the input, and totality with error localisation. -/
structure VerifiedUrlencoded where
  roundTrip : Spec.UrlencodeRoundTrip urlencodeL urldecodeL
  roundTripExt : Spec.UrlencodeRoundTripExt urlencodeL urldecodeL
  bytesRoundTrip : ∀ ps, urldecodeB (urlencodeB ps) = ps
  streaming : ∀ cfg, Spec.QsStreamingAgrees cfg
  total : ∀ cfg, Spec.QsTotal cfg

theorem theVerifiedUrlencoded : VerifiedUrlencoded where
  roundTrip := Qs.urldecode_urlencode
  roundTripExt := Qs.urlencode_urldecode_ext
  bytesRoundTrip := urldecodeB_urlencodeB
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

/-- Forms: `FormParser` fed any chunking equals one write, and Starlette's
limits hold of every accepted form. -/
structure VerifiedForm where
  streaming : Spec.FormStreamingAgrees
  urlencodedLimits : ∀ lim body fs, Starlette.parseUrlencodedRaw lim body = .ok fs →
    Spec.UrlencodedWithinLimits lim fs
  multipartLimits : ∀ lim ct body ps, Starlette.parseMultipartRaw lim ct body = .ok ps →
    Spec.MultipartWithinLimits lim ps

theorem theVerifiedForm : VerifiedForm where
  streaming := FormParser.write_chunks
  urlencodedLimits := Starlette.parseUrlencodedRaw_ok
  multipartLimits := Starlette.parseMultipartRaw_ok

end LeanMultipart
