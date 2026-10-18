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
runs the same machine into a `ByteArray` of UTF-8, taking each run of
literal bytes (no `%`) at once: one copy, then a fix-up of each `+` and
each byte `≥ 0x80` in place. `Proofs/Unquote.lean` proves the
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

/-! ## Plain ASCII

Outside an escape and a UTF-8 sequence, a byte below `0x80` that is not `%`
or `+` is its own character and its own UTF-8 byte. -/

/-- A byte that is not plain ASCII. -/
@[inline] def special (c : UInt8) : Bool := 0x80 ≤ c || c == Byte.PERCENT || c == Byte.PLUS

/-! ## Runs without `%`

Outside an escape and a UTF-8 sequence, every byte but `%` is a literal: `+`
is a space, a byte below `0x80` its own UTF-8 byte, a byte `c ≥ 0x80` the two
UTF-8 bytes of its Latin-1 character (`encByte`). A run of such bytes is
decoded by counting its bytes `≥ 0x80` (`countHigh`), copying it to the
output with that many bytes more, so that the output has exactly the room
the decoding takes, and writing in place: the copy is right as it stands
until the first `+` or byte `≥ 0x80`, and a `+` is overwritten with a space
(`fillA`); from the first byte `≥ 0x80` on, the output runs ahead of the
input, so each byte is written at its place (`fillB`). The writes carry
their bounds as proofs, so no write is checked at run time. -/

/-- The UTF-8 bytes of a literal byte. -/
def encByte (c : UInt8) : List UInt8 :=
  if c < 0x80 then [if c == Byte.PLUS then 0x20 else c]
  else if c < 0xC0 then [0xC2, c] else [0xC3, c - 0x40]

/-- The UTF-8 bytes of a run of literal bytes. -/
def encList (l : List UInt8) : List UInt8 := l.flatMap encByte

theorem encByte_length (c : UInt8) : (encByte c).length = if c < 0x80 then 1 else 2 := by
  unfold encByte; split
  · rfl
  · split <;> rfl

theorem encList_cons (c : UInt8) (l : List UInt8) :
    (encList (c :: l)).length = (encByte c).length + (encList l).length := by
  simp [encList]

/-- The bytes `b[i, stop)`. -/
def lits (b : ByteArray) (i stop : Nat) : List UInt8 := (b.data.toList.drop i).take (stop - i)

theorem lits_cons (b : ByteArray) (i stop : Nat) (h : i < stop) (hs : stop ≤ b.size) :
    lits b i stop = b[i] :: lits b (i + 1) stop := by
  unfold lits
  have hl : i < b.data.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons hl, show stop - i = (stop - (i + 1)) + 1 by omega, List.take_succ_cons]
  simp; rfl

theorem lits_nil (b : ByteArray) (i stop : Nat) (h : ¬ i < stop) : lits b i stop = [] := by
  unfold lits; rw [show stop - i = 0 by omega]; rfl

theorem usize_succ_lt (j : USize) (n : Nat) (h : j.toNat < n) (hn : n < USize.size) :
    (j + 1).toNat = j.toNat + 1 := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add]; simp only [USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)

theorem size_set' (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) : (a.set i v h).size = a.size := by
  cases a; exact Array.size_set _

theorem size_uset' (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_uset _

/-- Write the UTF-8 bytes of the literal bytes `b[i, stop)` from `j` on, in
place: `out` has room for all of them. -/
def fillB (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) (i j : USize) (out : ByteArray)
    (hw : out.size < USize.size) (hj : j.toNat + (encList (lits b i.toNat stop.toNat)).length ≤ out.size) :
    ByteArray :=
  if h : i < stop then
    have hi : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp h
    have hi1 : (i + 1).toNat = i.toNat + 1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    have hl := lits_cons b i.toNat stop.toNat hi hs
    let c := b.uget i (by omega)
    have hc : c = b[i.toNat] := rfl
    have hj' : j.toNat + (encByte c).length + (encList (lits b (i + 1).toNat stop.toNat)).length ≤ out.size := by
      rw [hl, encList_cons] at hj; rw [hc, hi1]; omega
    if h1 : c < 0x80 then
      have hlen : (encByte c).length = 1 := by rw [encByte_length]; simp [h1]
      have hjo : j.toNat < out.size := by omega
      have hj1 : (j + 1).toNat = j.toNat + 1 := usize_succ_lt j out.size hjo hw
      fillB b stop hs (i + 1) (j + 1) (out.uset j (if c == Byte.PLUS then 0x20 else c) hjo)
        (by rw [size_uset']; exact hw) (by rw [size_uset']; omega)
    else
      have hlen : (encByte c).length = 2 := by rw [encByte_length]; simp [h1]
      have hjo : j.toNat < out.size := by omega
      have hj1 : (j + 1).toNat = j.toNat + 1 := usize_succ_lt j out.size hjo hw
      have hjo1 : (j + 1).toNat < out.size := by omega
      have hj2 : (j + 2).toNat = j.toNat + 2 := usize_add_toNat j 2 (by omega)
      if c < 0xC0 then
        fillB b stop hs (i + 1) (j + 2) ((out.uset j 0xC2 hjo).uset (j + 1) c (by rw [size_uset']; exact hjo1))
          (by rw [size_uset', size_uset']; exact hw) (by rw [size_uset', size_uset']; omega)
      else
        fillB b stop hs (i + 1) (j + 2) ((out.uset j 0xC3 hjo).uset (j + 1) (c - 0x40) (by rw [size_uset']; exact hjo1))
          (by rw [size_uset', size_uset']; exact hw) (by rw [size_uset', size_uset']; omega)
  else out
termination_by stop.toNat - i.toNat
decreasing_by all_goals omega

/-- A byte `fillA` stops at: `+`, or one `≥ 0x80`. -/
@[inline] def litStop (c : UInt8) : Bool := 0x80 ≤ c || c == Byte.PLUS

theorem encByte_plain (c : UInt8) (hp : litStop c = false) : encByte c = [c] := by
  simp only [litStop, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hp
  have hlt : c < 0x80 := UInt8.not_le.mp hp.1
  have hplus : (c == Byte.PLUS) = false := hp.2
  simp [encByte, hlt, hplus]

theorem copy_size (b out : ByteArray) (i n : Nat) (h : i + n ≤ b.size) :
    (b.copySlice i out out.size n false).size = out.size + n := by
  rw [copySlice_end, ByteArray.size_append, ByteArray.size_extract]; omega

theorem encList_length_le (l : List UInt8) : (encList l).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [encList]
  | cons c l ih => rw [encList_cons, encByte_length, List.length_cons]; split <;> omega

theorem shr7 (c : UInt8) : (c >>> 7).toUSize.toNat = if c < 0x80 then 0 else 1 := by
  have hc : c.toNat < 256 := c.toNat_lt
  rw [UInt8.toNat_toUSize, UInt8.toNat_shiftRight]
  simp only [UInt8.lt_iff_toNat_lt, Nat.shiftRight_eq_div_pow]
  split <;> simp_all <;> omega

/-- `acc` plus the number of bytes `≥ 0x80` in `b[i, stop)`: how much longer
their UTF-8 is than they are. -/
def countHigh (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) (i acc : USize) : USize :=
  if h : i < stop then
    countHigh b stop hs (i + 1) (acc + (b.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega) >>> 7).toUSize)
  else acc
termination_by stop.toNat - i.toNat
decreasing_by
  have := usize_succ_lt i stop.toNat (USize.lt_iff_toNat_lt.mp h) stop.toNat_lt_two_pow_numBits
  rw [USize.lt_iff_toNat_lt] at h
  omega

theorem countHigh_spec (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i acc : USize), stop.toNat - i.toNat = n → acc.toNat + n < USize.size →
      (countHigh b stop hs i acc).toNat + (lits b i.toNat stop.toNat).length =
        acc.toNat + (encList (lits b i.toNat stop.toNat)).length := by
  intro n
  induction n with
  | zero =>
    intro i acc hn _
    rw [countHigh.eq_1]
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    simp [h1, lits_nil b _ _ (show ¬ i.toNat < stop.toNat by omega), encList]
  | succ n ih =>
    intro i acc hn hw
    have hi : i.toNat < stop.toNat := by omega
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; exact hi
    have hi1 := usize_succ_lt i stop.toNat hi stop.toNat_lt_two_pow_numBits
    have hget : b.uget i (by omega) = b[i.toNat] := rfl
    rw [countHigh.eq_1]
    simp only [h1, ↓reduceDIte, hget]
    rw [lits_cons b i.toNat stop.toNat hi hs]
    have hd := shr7 b[i.toNat]
    have hacc : (acc + (b[i.toNat] >>> 7).toUSize).toNat = acc.toNat + (b[i.toNat] >>> 7).toUSize.toNat := by
      have hs2 : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by split at hd <;> omega)
    have := ih (i + 1) (acc + (b[i.toNat] >>> 7).toUSize) (by omega) (by rw [hacc]; split at hd <;> omega)
    rw [hi1, hacc] at this
    rw [encList_cons, encByte_length, List.length_cons]
    split at hd <;> rename_i hc <;> simp only [hc, ↓reduceIte] <;> omega

/-- `out` holds the literal bytes `b[i, stop)` from `j` on, and ends there:
turn each `+` into a space in place, until a byte `≥ 0x80`; from there on,
count the bytes `≥ 0x80` left, extend `out` by that many, and let `fillB`
write. -/
def fillA (b : ByteArray) (stop : USize) (hs : stop.toNat ≤ b.size) (i j : USize) (out : ByteArray)
    (hw : out.size + (stop.toNat - i.toNat) < USize.size) (hj : j.toNat + (stop.toNat - i.toNat) ≤ out.size) :
    ByteArray :=
  let k := scanUntilU8 b litStop stop hs i
  have hkN : k.toNat = scanUntil b litStop stop.toNat i.toNat := scanUntilU8_eq b litStop stop hs _ i rfl
  have hki : i.toNat ≤ k.toNat := hkN ▸ scanUntil_ge b litStop stop.toNat _ i.toNat rfl
  if h : k < stop then
    have hk : k.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp h
    have hik : (k - i).toNat = k.toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hki)
    have hj' : (j + (k - i)).toNat = j.toNat + (k.toNat - i.toNat) := by
      have hs2 : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [USize.toNat_add, hik]; exact Nat.mod_eq_of_lt (by omega)
    have hjo : (j + (k - i)).toNat < out.size := by omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := usize_succ_lt k stop.toNat hk stop.toNat_lt_two_pow_numBits
    if b.uget k (by omega) == Byte.PLUS then
      have hj1 : (j + (k - i) + 1).toNat = j.toNat + (k.toNat - i.toNat) + 1 := by
        rw [usize_succ_lt _ out.size hjo (by omega), hj']
      fillA b stop hs (k + 1) (j + (k - i) + 1) (out.uset (j + (k - i)) 0x20 hjo)
        (by rw [size_uset', hk1]; omega) (by rw [size_uset', hk1, hj1]; omega)
    else
      let x := countHigh b stop hs k 0
      have hx : x.toNat + (stop.toNat - k.toNat) = (encList (lits b k.toNat stop.toNat)).length := by
        have := countHigh_spec b stop hs (stop.toNat - k.toNat) k 0 rfl (by simp; omega)
        have hl : (lits b k.toNat stop.toNat).length = stop.toNat - k.toNat := by simp [lits]; omega
        simp only [USize.toNat_zero, Nat.zero_add, hl] at this
        exact this
      have hxle : x.toNat ≤ stop.toNat - k.toNat := by
        have := encList_length_le (lits b k.toNat stop.toNat)
        have hl : (lits b k.toNat stop.toNat).length = stop.toNat - k.toNat := by simp [lits]; omega
        omega
      have hsz : (b.copySlice k.toNat out out.size x.toNat false).size = out.size + x.toNat :=
        copy_size b out k.toNat _ (by omega)
      fillB b stop hs k (j + (k - i)) (b.copySlice k.toNat out out.size x.toNat false)
        (by rw [hsz]; omega) (by rw [hj', hsz]; omega)
  else out
termination_by stop.toNat - i.toNat
decreasing_by
  have h1 : (scanUntilU8 b litStop stop hs i).toNat < stop.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 := usize_succ_lt (scanUntilU8 b litStop stop hs i) stop.toNat h1 stop.toNat_lt_two_pow_numBits
  have h3 := scanUntilU8_eq b litStop stop hs _ i rfl
  have _h4 := scanUntil_ge b litStop stop.toNat _ i.toNat rfl
  omega

/-- The length of the run without `%` at `i`, before `stop`. -/
def litSpan (s : St ByteArray) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.pct, s.u8 with
  | .none, .idle => scanFor b Byte.PERCENT stop i - i
  | _, _ => 0

/-- Decode the `n` literal bytes at `i`: copy them, then write in place. -/
def litBulk (s : St ByteArray) (b : ByteArray) (i n : Nat) : St ByteArray :=
  if n = 0 then s
  else if h : i + n ≤ b.size ∧ b.size < USize.size ∧ s.out.size + 2 * n < USize.size then
    have h1 : (b.copySlice i s.out s.out.size n false).size = s.out.size + n := copy_size b s.out i n h.1
    have e1 : (i + n).toUSize.toNat = i + n := toNat_toUSize (by omega)
    have e2 : i.toUSize.toNat = i := toNat_toUSize (by omega)
    have e3 : s.out.size.toUSize.toNat = s.out.size := toNat_toUSize (by omega)
    let out := fillA b (i + n).toUSize (by rw [e1]; exact h.1) i.toUSize s.out.size.toUSize
      (b.copySlice i s.out s.out.size n false) (by rw [h1, e1, e2]; omega) (by rw [h1, e1, e2, e3]; omega)
    { s with out := out }
  else ((b.data.toList.drop i).take n).foldl step s

end Unquote

open Unquote in
/-- Starlette's `unquote_plus(raw.decode("latin-1"))`, the specification:
the machine run over the bytes, pushing characters onto a string. -/
def unquotePlusLatin1 (raw : ByteArray) : String :=
  finish (raw.data.toList.foldl step ({ out := "" } : St String))

end LeanMultipart
