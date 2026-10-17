import LeanMultipart.APIs
import LeanMultipart.Proofs.Verified

/-!
# LeanMultipart

A clean-room port of python-multipart to Lean 4: multipart/form-data and application/x-www-form-urlencoded parsers proved against their printers.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
