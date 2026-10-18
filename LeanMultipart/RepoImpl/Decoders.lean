import LeanMultipart.RepoImpl.Percent

/-!
# Content-Transfer-Encoding decoders

Upstream's `Base64Decoder` and `QuotedPrintableDecoder`, which wrap
`binascii.a2b_base64` (non-strict) and `binascii.a2b_qp`.

* `a2bBase64L` is non-strict `a2b_base64`: bytes outside the alphabet are
  skipped; a pad `=` after at least two data characters of a quad that
  completes it stops decoding; a quad left incomplete at the end is an error.
* `a2bQpL` is `a2b_qp` with `header=False`: `=XX` (hex of either case) is
  the byte, `=` before a line end is a soft line break, `==` is `=`, and any
  other `=` is kept literally. A trailing `=` is dropped.

The streaming decoders cache input exactly as upstream does: base64 decodes
the longest multiple-of-four prefix of what it has and keeps the rest;
quoted-printable holds back the last two bytes if they contain `=`.
-/

namespace LeanMultipart

/-- The value of a base64 alphabet byte. -/
def b64Val? (c : UInt8) : Option Nat :=
  if Byte.isUpper c then some (c.toNat - 65)
  else if Byte.isLower c then some (c.toNat - 71)
  else if Byte.isDigit c then some (c.toNat + 4)
  else if c == 43 then some 62
  else if c == 47 then some 63
  else none

inductive DecodeError where
  /-- "Incorrect padding" / a quad left incomplete. -/
  | base64Padding
  /-- Bytes left in the base64 cache at `finalize`. -/
  | base64Leftover (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Non-strict `a2b_base64`. `quad` is the number of data characters seen in
the current quad, `left` the bits carried, `pads` the pad run. -/
def a2bBase64Go : Bytes → Nat → Nat → Nat → Array UInt8 → Except DecodeError (Array UInt8)
  | [], quad, _, _, out => if quad == 0 then .ok out else .error .base64Padding
  | c :: rest, quad, left, pads, out =>
    if c == Byte.EQ then
      if 2 ≤ quad && 4 ≤ quad + (pads + 1) then .ok out
      else a2bBase64Go rest quad left (pads + 1) out
    else match b64Val? c with
      | none => a2bBase64Go rest quad left pads out
      | some v =>
        match quad with
        | 0 => a2bBase64Go rest 1 v 0 out
        | 1 => a2bBase64Go rest 2 (v % 16) 0 (out.push (left * 4 + v / 16).toUInt8)
        | 2 => a2bBase64Go rest 3 (v % 4) 0 (out.push ((left % 16) * 16 + v / 4).toUInt8)
        | _ => a2bBase64Go rest 0 0 0 (out.push ((left % 4) * 64 + v).toUInt8)

def a2bBase64L (l : Bytes) : Except DecodeError (Array UInt8) := a2bBase64Go l 0 0 0 #[]

def isHexDigit (c : UInt8) : Bool := (hexVal? c).isSome

/-- Drop through the next `LF`, inclusive. -/
def skipPastLF : Bytes → Bytes
  | [] => []
  | c :: r => if c == Byte.LF then r else skipPastLF r

theorem skipPastLF_length_le (l : Bytes) : (skipPastLF l).length ≤ l.length := by
  induction l with
  | nil => simp [skipPastLF]
  | cons c r ih => simp only [skipPastLF]; split <;> simp <;> omega

/-- `a2b_qp`, `header=False`. -/
def a2bQpGo : Bytes → Array UInt8 → Array UInt8
  | [], out => out
  | [c], out => if c == Byte.EQ then out else out.push c
  | c :: d :: rest, out =>
    if c == Byte.EQ then
      if d == Byte.LF then a2bQpGo rest out
      else if d == Byte.CR then a2bQpGo (skipPastLF rest) out
      else if d == Byte.EQ then a2bQpGo rest (out.push Byte.EQ)
      else match rest with
        | e :: rest' =>
          match hexVal? d, hexVal? e with
          | some x, some y => a2bQpGo rest' (out.push (x * 16 + y).toUInt8)
          | _, _ => a2bQpGo (d :: e :: rest') (out.push Byte.EQ)
        | [] => a2bQpGo [d] (out.push Byte.EQ)
    else a2bQpGo (d :: rest) (out.push c)
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact Nat.lt_of_le_of_lt (skipPastLF_length_le _) (by omega)

def a2bQpL (l : Bytes) : Array UInt8 := a2bQpGo l #[]

/-- Upstream's `Base64Decoder`. -/
structure Base64Decoder where
  cache : Bytes := []
  out : Array UInt8 := #[]

namespace Base64Decoder

def write (d : Base64Decoder) (chunk : ByteArray) : Except DecodeError Base64Decoder := do
  let data := d.cache ++ chunk.data.toList
  let n := (data.length / 4) * 4
  let decoded ← if n == 0 then pure #[] else a2bBase64L (data.take n)
  pure { cache := data.drop n, out := d.out ++ decoded }

def finalize (d : Base64Decoder) : Except DecodeError ByteArray :=
  if d.cache.isEmpty then .ok ⟨d.out⟩ else .error (.base64Leftover d.cache.length)

end Base64Decoder

/-- Upstream's `QuotedPrintableDecoder`. -/
structure QuotedPrintableDecoder where
  cache : Bytes := []
  out : Array UInt8 := #[]

namespace QuotedPrintableDecoder

def write (d : QuotedPrintableDecoder) (chunk : ByteArray) : QuotedPrintableDecoder :=
  let data := d.cache ++ chunk.data.toList
  let tail := data.drop (data.length - 2)
  if tail.contains Byte.EQ then
    { cache := tail, out := d.out ++ a2bQpL (data.take (data.length - 2)) }
  else { cache := [], out := d.out ++ a2bQpL data }

def finalize (d : QuotedPrintableDecoder) : ByteArray :=
  if d.cache.isEmpty then ⟨d.out⟩ else ⟨d.out ++ a2bQpL d.cache⟩

end QuotedPrintableDecoder

/-- A whole body through a fresh `Base64Decoder` in one write. -/
def decodeBase64 (b : ByteArray) : Except DecodeError ByteArray := do
  let d ← ({} : Base64Decoder).write b
  d.finalize

/-- A whole body through a fresh `QuotedPrintableDecoder` in one write. -/
def decodeQuotedPrintable (b : ByteArray) : ByteArray :=
  (({} : QuotedPrintableDecoder).write b).finalize

end LeanMultipart
