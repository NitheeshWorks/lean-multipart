import LeanMultipart.RepoImpl.Percent
import LeanMultipart.Theory.Machine

/-!
# Starlette's field decoding: `unquote_plus(raw.decode("latin-1"))`

Starlette's `FormParser` decodes each urlencoded name and value with
`urllib.parse.unquote_plus(raw.decode("latin-1"))`. Read on the raw bytes,
CPython's algorithm is:

* `+` is a space;
* `%XY` (two hex digits, either case) is the byte `XY`, and each run of such
  bytes, between the other characters, is decoded as UTF-8 with
  `errors="replace"`: one U+FFFD for each maximal invalid subpart, as
  CPython's decoder emits;
* any other byte is the character of that Latin-1 code (ASCII as itself).

(CPython splits the string into ASCII runs and decodes each run's
`unquote_to_bytes` as UTF-8; a literal ASCII byte ends any incomplete UTF-8
sequence, so this is the same as decoding each run of escapes alone.)

`unquotePlusLatin1` is that algorithm as a byte machine whose output is a
`String`, pushed a character at a time: the specification. The machine is
generic in where the characters go (`Sink`), and `unquotePlusLatin1Fast`
runs the same machine into a `ByteArray` of UTF-8, taking each run of plain
ASCII bytes (no `%`, no `+`) with one copy. `Proofs/Unquote.lean` proves the
two equal, and marks that `@[csimp]`, so compiled code runs the fast one.
-/

namespace LeanMultipart
namespace Unquote

/-- Where decoded characters go. -/
class Sink (α : Type) where
  push : α → Char → α

/-- The specification's sink: a string. -/
instance : Sink String := ⟨String.push⟩

/-- The fast sink: the UTF-8 bytes of the string (an ASCII character is one byte). -/
def pushUtf8 (out : ByteArray) (c : Char) : ByteArray :=
  if c.val.toNat ≤ 0x7f then out.push (UInt8.ofNat c.val.toNat)
  else out ++ (String.utf8EncodeChar c).toByteArray

instance : Sink ByteArray := ⟨pushUtf8⟩

/-- Progress through a `%XY` escape. -/
inductive Pct where
  | none
  | pct
  | hex (a : UInt8) (x : Nat)

/-- Progress through a UTF-8 sequence of escaped bytes: none, or `need` more
continuation bytes, the next one in `lo..hi`, and the code point so far. -/
inductive U8 where
  | idle
  | seq (need : Nat) (lo hi : UInt8) (cp : Nat)

structure St (α : Type) where
  out : α
  pct : Pct := .none
  u8 : U8 := .idle

variable {α : Type} [Sink α]

def emit (s : St α) (c : Char) : St α := { s with out := Sink.push s.out c }

/-- U+FFFD, for an invalid or incomplete UTF-8 sequence. -/
def replacement : Char := '�'

/-- The first byte of a UTF-8 sequence (CPython's ranges, so overlong forms
and surrogates are invalid). -/
def startByte (s : St α) (v : UInt8) : St α :=
  if v < 0x80 then emit s (Char.ofNat v.toNat)
  else if 0xC2 ≤ v && v ≤ 0xDF then { s with u8 := .seq 1 0x80 0xBF (v.toNat % 32) }
  else if v == 0xE0 then { s with u8 := .seq 2 0xA0 0xBF (v.toNat % 16) }
  else if v == 0xED then { s with u8 := .seq 2 0x80 0x9F (v.toNat % 16) }
  else if 0xE1 ≤ v && v ≤ 0xEF then { s with u8 := .seq 2 0x80 0xBF (v.toNat % 16) }
  else if v == 0xF0 then { s with u8 := .seq 3 0x90 0xBF (v.toNat % 8) }
  else if v == 0xF4 then { s with u8 := .seq 3 0x80 0x8F (v.toNat % 8) }
  else if 0xF1 ≤ v && v ≤ 0xF3 then { s with u8 := .seq 3 0x80 0xBF (v.toNat % 8) }
  else emit s replacement

/-- A byte from an escape: continue or start a UTF-8 sequence. A byte that
does not continue the sequence ends it with U+FFFD and is read afresh. -/
def escByte (s : St α) (v : UInt8) : St α :=
  match s.u8 with
  | .idle => startByte s v
  | .seq need lo hi cp =>
    if lo ≤ v && v ≤ hi then
      let cp := cp * 64 + v.toNat % 64
      if need ≤ 1 then emit { s with u8 := .idle } (Char.ofNat cp)
      else { s with u8 := .seq (need - 1) 0x80 0xBF cp }
    else startByte (emit { s with u8 := .idle } replacement) v

/-- A literal character ends any UTF-8 sequence in progress. -/
def lit (s : St α) (c : Char) : St α :=
  match s.u8 with
  | .idle => emit s c
  | .seq .. => emit (emit { s with u8 := .idle } replacement) c

/-- A literal byte: `+` is a space, any other byte its Latin-1 character. -/
def litByte (s : St α) (b : UInt8) : St α :=
  lit s (if b == Byte.PLUS then ' ' else Char.ofNat b.toNat)

/-- A byte outside an escape. -/
def plain (s : St α) (b : UInt8) : St α :=
  if b == Byte.PERCENT then { s with pct := .pct } else litByte s b

/-- One byte. -/
def step (s : St α) (b : UInt8) : St α :=
  match s.pct with
  | .none => plain s b
  | .pct =>
    match hexVal? b with
    | some x => { s with pct := .hex b x }
    | none => plain (lit { s with pct := .none } '%') b
  | .hex a x =>
    match hexVal? b with
    | some y => escByte { s with pct := .none } (x * 16 + y).toUInt8
    | none => plain (litByte (lit { s with pct := .none } '%') a) b

/-- End of input: an unfinished escape is literal, an unfinished UTF-8
sequence is U+FFFD. -/
def finish (s : St α) : α :=
  let s := match s.pct with
    | .none => s
    | .pct => lit { s with pct := .none } '%'
    | .hex a _ => litByte (lit { s with pct := .none } '%') a
  match s.u8 with
  | .idle => s.out
  | .seq .. => (emit s replacement).out

/-! ## Runs of plain ASCII

Outside an escape and a UTF-8 sequence, a byte below `0x80` that is not `%`
or `+` is its own character and its own UTF-8 byte. -/

/-- A byte that `plainSpan` stops at. -/
@[inline] def special (c : UInt8) : Bool := 0x80 ≤ c || c == Byte.PERCENT || c == Byte.PLUS

/-- The length of the run of plain ASCII at `i`, before `stop`. -/
def plainSpan (s : St ByteArray) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.pct, s.u8 with
  | .none, .idle => scanUntil b special stop i - i
  | _, _ => 0

/-- Copy the `n` bytes at `i` to the output. -/
def plainBulk (s : St ByteArray) (b : ByteArray) (i n : Nat) : St ByteArray :=
  if n = 0 then s else { s with out := b.copySlice i s.out s.out.size n false }

end Unquote

open Unquote in
/-- Starlette's `unquote_plus(raw.decode("latin-1"))`, the specification:
the machine run over the bytes, pushing characters onto a string. -/
def unquotePlusLatin1 (raw : ByteArray) : String :=
  finish (raw.data.toList.foldl step ({ out := "" } : St String))

end LeanMultipart
