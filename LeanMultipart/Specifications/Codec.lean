import LeanMultipart.RepoImpl.Form

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

/-- The streaming querystring parser fed any chunking agrees with the
whole-buffer parser. -/
def QsStreamingAgrees (cfg : QsConfig) : Prop :=
  ∀ cs : List Bytes, Qs.result (Qs.feedChunks cfg {} cs) = Qs.parseL cfg cs.flatten

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
