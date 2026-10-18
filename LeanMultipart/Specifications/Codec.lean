import LeanMultipart.RepoImpl

/-!
# Specifications: percent-encoding and urlencoded forms

The properties, stated in `Prop`. Each is proved in `Proofs/` and has a slot
in `Proofs/Verified.lean`.
-/

namespace LeanMultipart.Spec

/-- Percent-decoding undoes percent-encoding on any continuation. -/
def PercentRoundTrip (enc dec : Bytes → Bytes) : Prop :=
  ∀ l rest, dec (enc l ++ rest) = l ++ dec rest

/-- Decoding what `urlencode` printed gives back the pairs. -/
def UrlencodeRoundTrip (enc : List (Bytes × Bytes) → Bytes) (dec : Bytes → List (Bytes × Bytes)) : Prop :=
  ∀ ps, dec (enc ps) = ps

/-- The `_ext` form: pairs, a `&`, then any continuation. -/
def UrlencodeRoundTripExt (enc : List (Bytes × Bytes) → Bytes) (dec : Bytes → List (Bytes × Bytes)) : Prop :=
  ∀ ps rest, dec (enc ps ++ [Byte.AMP] ++ rest) = ps ++ dec rest

/-- The streaming `QuerystringParser`, fed any split of the input and its
callbacks collected, gives the whole-buffer result. -/
def QsStreamingAgrees (cfg : QsConfig) : Prop :=
  ∀ chunks : List ByteArray, QuerystringParser.parseChunks cfg chunks = Qs.parse cfg (concatChunks chunks)

/-- The querystring parser is total: it processes `min(len, maxSize)` bytes
and reports errors inside them. -/
def QsTotal (cfg : QsConfig) : Prop :=
  ∀ l, Qs.processed cfg l = Qs.room cfg {} l.length ∧
    ∀ e, Qs.parseL cfg l = .error e → e.offset < Qs.processed cfg l

/-- What `parseQuerystring` promises about its result. -/
def QsParseSpec (cfg : QsConfig) (body : ByteArray) (r : Except QsError (List QsField)) : Prop :=
  (∀ cs : List Bytes, cs.flatten = body.data.toList → Qs.result (Qs.feedChunks cfg {} cs) = r) ∧
    ∀ e, r = .error e → e.offset < body.size

end LeanMultipart.Spec
