/-!
# `hashlib.sha256`, for the examples

The in-depth example in python-multipart's `docs/index.md` hashes each
uploaded part with Python's `hashlib.sha256()`. Lean's standard library has
no SHA-256, so this helper gives the three calls the example uses:
`Hashlib.sha256`, `.update data` and `.hexdigest` (FIPS 180-4). It is a
helper of the examples, not part of the library.
-/

namespace Hashlib

private def roundK : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- A running SHA-256: the chaining value, the bytes of an unfinished
block, and the length so far. -/
structure Sha256 where
  h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  pending : ByteArray := .empty
  length : Nat := 0

/-- `hashlib.sha256()`. -/
def sha256 : Sha256 := {}

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One 64-byte block of `b` at `off`. -/
private def compress (hv : Array UInt32) (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    let j := off + 4 * i
    w := w.push ((b[j]!.toUInt32 <<< 24) ||| (b[j+1]!.toUInt32 <<< 16) ||| (b[j+2]!.toUInt32 <<< 8) ||| b[j+3]!.toUInt32)
  for i in [16:64] do
    let x := w[i-15]!
    let y := w[i-2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := hv[0]!
  let mut b' := hv[1]!
  let mut c := hv[2]!
  let mut d := hv[3]!
  let mut e := hv[4]!
  let mut f := hv[5]!
  let mut g := hv[6]!
  let mut hh := hv[7]!
  for i in [0:64] do
    let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + roundK[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b') ^^^ (a &&& c) ^^^ (b' &&& c))
    hh := g; g := f; f := e; e := d + t1; d := c; c := b'; b' := a; a := t1 + t2
  return #[hv[0]! + a, hv[1]! + b', hv[2]! + c, hv[3]! + d, hv[4]! + e, hv[5]! + f, hv[6]! + g, hv[7]! + hh]

/-- Hash the full blocks of `buf`; keep the rest pending. -/
private def absorb (s : Sha256) (buf : ByteArray) (length : Nat) : Sha256 :=
  let n := buf.size / 64
  let h := (List.range n).foldl (fun h j => compress h buf (64 * j)) s.h
  { h, pending := buf.extract (64 * n) buf.size, length }

/-- `hash.update(data)`. -/
def Sha256.update (s : Sha256) (data : ByteArray) : Sha256 :=
  absorb s (s.pending ++ data) (s.length + data.size)

/-- `hash.digest()`: the 32-byte digest. -/
def Sha256.digest (s : Sha256) : ByteArray := Id.run do
  let mut tail := s.pending.push 0x80
  while tail.size % 64 != 56 do tail := tail.push 0
  let bits := s.length * 8
  for i in [0:8] do tail := tail.push (bits >>> (8 * (7 - i))).toUInt8
  let h := (absorb s tail 0).h
  let mut out := ByteArray.empty
  for x in h do
    for i in [0:4] do out := out.push (x >>> (8 * (3 - i).toUInt32)).toUInt8
  return out

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

/-- `hash.hexdigest()`. -/
def Sha256.hexdigest (s : Sha256) : String :=
  String.ofList (s.digest.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

end Hashlib
