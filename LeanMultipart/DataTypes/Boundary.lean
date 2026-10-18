import LeanMultipart.DataTypes.Bytes

/-!
# The multipart boundary

A `Boundary` is a byte string that satisfies `ValidBoundary`: between 1 and
`maxBoundaryLength` bytes, every byte an RFC 2046 `bchar`, and the last byte
not a space. The invariant is a field, so a `Boundary` value cannot be built
without the proof.

The length bound is upstream's `MAX_BOUNDARY_LENGTH = 256`, not RFC 2046's
70: upstream accepts any boundary up to 256 bytes
(`tests/test_multipart.py::test_boundary_too_long`) and real clients send
boundaries longer than 70. The `bchar` restriction is stricter than upstream,
which accepts any byte; it is what makes the delimiter `CR LF - - boundary`
contain `CR` only at its first byte, which the round-trip proof uses.
-/

namespace LeanMultipart

/-- Upstream's `MAX_BOUNDARY_LENGTH`. -/
def maxBoundaryLength : Nat := 256

/-- The boundary refinement, on a list of bytes. -/
def ValidBoundaryL (b : Bytes) : Prop :=
  1 ≤ b.length ∧ b.length ≤ maxBoundaryLength ∧ (∀ c ∈ b, Byte.isBoundaryChar c = true) ∧
    b.getLast? ≠ some Byte.SPACE

instance (b : Bytes) : Decidable (ValidBoundaryL b) := by
  unfold ValidBoundaryL; exact inferInstance

/-- The boundary refinement on a `ByteArray`. -/
def ValidBoundary (b : ByteArray) : Prop := ValidBoundaryL b.data.toList

instance (b : ByteArray) : Decidable (ValidBoundary b) := by
  unfold ValidBoundary; exact inferInstance

/-- A multipart boundary, with its validity as a field. -/
structure Boundary where
  bytes : ByteArray
  h_valid : ValidBoundary bytes

namespace Boundary

/-- The boundary as a list. -/
def toList (b : Boundary) : Bytes := b.bytes.data.toList

/-- The delimiter that separates parts: `CR LF - -` then the boundary. -/
def delimL (b : Boundary) : Bytes := [Byte.CR, Byte.LF, Byte.HYPHEN, Byte.HYPHEN] ++ b.toList

/-- The delimiter as a byte array. -/
def delim (b : Boundary) : ByteArray := ⟨b.delimL.toArray⟩

/-- Validate a byte string as a boundary. -/
def ofBytes? (b : ByteArray) : Option Boundary :=
  if h : ValidBoundary b then some ⟨b, h⟩ else none

end Boundary

end LeanMultipart
