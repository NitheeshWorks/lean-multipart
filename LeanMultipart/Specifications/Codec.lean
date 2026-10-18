import LeanMultipart.RepoImpl
import LeanMultipart.Specifications.Multipart

/-!
# Specifications: the codecs

The round trips, each an equation about public functions, on any
continuation of the buffer where the format allows one. Each is proved in
`Proofs/` as an instance of the codec theory (`Theory/Codec.lean`) and has
a slot in `Proofs/Verified.lean`.
-/

namespace LeanMultipart.Spec

/-- `unquote_to_bytes (quote b + rest) = b + unquote_to_bytes rest`. -/
def PercentRoundTrip : Prop :=
  ∀ b rest : ByteArray, percentDecode (percentEncode b ++ rest) = b ++ percentDecode rest

/-- `unquote_plus (quote_plus b + rest) = b + unquote_plus rest`. -/
def QuotePlusRoundTrip : Prop :=
  ∀ b rest : ByteArray, unquotePlus (quotePlus b ++ rest) = b ++ unquotePlus rest

/-- Decoding what `urlencode` printed gives back the pairs. -/
def UrlencodeRoundTrip : Prop := ∀ ps, urldecodeB (urlencodeB ps) = ps

/-- The same, followed by `&` and any continuation. -/
def UrlencodeRoundTripExt : Prop :=
  ∀ ps (rest : ByteArray), urldecodeB (urlencodeB ps ++ ⟨#[Byte.AMP]⟩ ++ rest) = ps ++ urldecodeB rest

/-- The `name` and `filename` a form part is printed with are read back. -/
def DispositionRoundTrip : Prop :=
  ∀ (n : ByteArray) (f ct : Option ByteArray) (body : ByteArray), Options.SafeParam n.data.toList →
    (∀ x, f = some x → Options.SafeParam x.data.toList) →
    dispositionParams (formPart n f ct body).headers = (some n.data.toList, f.map (·.data.toList))

/-- The querystring parser is total: it processes `min(len, maxSize)` bytes
and reports errors inside them. -/
def QsTotal (cfg : QsConfig) : Prop :=
  ∀ l, Qs.processed cfg l = Qs.room cfg {} l.length ∧
    ∀ e, Qs.parseL cfg l = .error e → e.offset < Qs.processed cfg l

/-- The streaming `QuerystringParser`, fed any split of the input and its
callbacks collected, gives the whole-buffer result. -/
def QsStreamingAgrees (cfg : QsConfig) : Prop :=
  ∀ chunks : List ByteArray, QuerystringParser.parseChunks cfg chunks = Qs.parse cfg (concatChunks chunks)

/-- What `parseQuerystring` promises about its result. -/
def QsParseSpec (cfg : QsConfig) (body : ByteArray) (r : Except QsError (List QsField)) : Prop :=
  (∀ chunks : List ByteArray, concatChunks chunks = body → QuerystringParser.parseChunks cfg chunks = r) ∧
    ∀ e, r = .error e → e.offset < body.size

end LeanMultipart.Spec
