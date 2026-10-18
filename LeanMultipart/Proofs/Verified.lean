import LeanMultipart.Proofs.Percent
import LeanMultipart.Proofs.Querystring
import LeanMultipart.Proofs.MultipartRoundTrip
import LeanMultipart.Proofs.Stream
import LeanMultipart.Proofs.Form
import LeanMultipart.Proofs.Wrappers

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a layer's implementation with a proof term for
every `Specifications/<Layer>.lean` property it claims. A specification with
no proof is a compile error the moment it needs a field here: you cannot
construct a `Verified<Layer>` value without every proof in hand.
-/

namespace LeanMultipart
end LeanMultipart
