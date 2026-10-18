import LeanMultipart.RepoImpl.Unquote

/-!
# The fast field decoder is the specification

`unquotePlusLatin1` (the machine pushing characters onto a `String`) and
`unquotePlusLatin1Fast` (the same machine writing UTF-8 bytes, copying runs
of plain ASCII at once) are equal, so `@[csimp]` lets compiled code run the
fast one wherever the specification is called.

The argument has two steps. The machine is generic in its `Sink`, and
`String.toByteArray` turns pushing a character onto a string into pushing
its UTF-8 bytes (`toByteArray_push`), so running on bytes is running on the
string and encoding (`foldl_toBytes`). And a run of plain ASCII, folded byte
by byte, appends those bytes (`foldl_plain`), which is what the copy does
(`plainBulk_eq`), so `bytesFoldRun_eq` applies.
-/

namespace LeanMultipart
namespace Unquote

/-- The byte-sink state for a string-sink state. -/
def toBytes (s : St String) : St ByteArray := { out := s.out.toByteArray, pct := s.pct, u8 := s.u8 }

theorem ascii_val (c : UInt8) (h : c < 0x80) : (Char.ofNat c.toNat).val.toNat = c.toNat := by
  have hc : c.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h
  have hv : c.toNat.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux]

@[simp] theorem toBytes_pct (s : St String) : (toBytes s).pct = s.pct := rfl
@[simp] theorem toBytes_u8 (s : St String) : (toBytes s).u8 = s.u8 := rfl
theorem toBytes_with_pct (s : St String) (p : Pct) : toBytes { s with pct := p } = { toBytes s with pct := p } := rfl
theorem toBytes_with_u8 (s : St String) (u : U8) : toBytes { s with u8 := u } = { toBytes s with u8 := u } := rfl

theorem pushUtf8_toByteArray (s : String) (c : Char) :
    pushUtf8 s.toByteArray c = (s.push c).toByteArray := by
  rw [String.toByteArray_push, List.utf8Encode_singleton]
  unfold pushUtf8
  split
  · rename_i h
    simp only [String.utf8EncodeChar, h, ↓reduceIte, ByteArray.append_toByteArray_singleton]
  · rfl

theorem emit_toBytes (s : St String) (c : Char) : toBytes (emit s c) = emit (toBytes s) c := by
  show ({ out := (s.out.push c).toByteArray, pct := s.pct, u8 := s.u8 } : St ByteArray) =
    { out := pushUtf8 s.out.toByteArray c, pct := s.pct, u8 := s.u8 }
  rw [pushUtf8_toByteArray]

theorem startByte_toBytes (s : St String) (v : UInt8) : toBytes (startByte s v) = startByte (toBytes s) v := by
  unfold startByte
  repeat' split
  all_goals first | exact emit_toBytes s _ | rfl

theorem lit_toBytes (s : St String) (c : Char) : toBytes (lit s c) = lit (toBytes s) c := by
  unfold lit
  rw [toBytes_u8]
  cases s.u8 with
  | idle => exact emit_toBytes s c
  | seq _ _ _ _ => dsimp only; rw [emit_toBytes, emit_toBytes, toBytes_with_u8]

theorem litByte_toBytes (s : St String) (b : UInt8) : toBytes (litByte s b) = litByte (toBytes s) b := by
  unfold litByte; exact lit_toBytes s _

theorem plain_toBytes (s : St String) (b : UInt8) : toBytes (plain s b) = plain (toBytes s) b := by
  unfold plain; split
  · rfl
  · exact litByte_toBytes s b

theorem escByte_toBytes (s : St String) (v : UInt8) : toBytes (escByte s v) = escByte (toBytes s) v := by
  unfold escByte
  rw [toBytes_u8]
  cases s.u8 with
  | idle => exact startByte_toBytes s v
  | seq need lo hi cp =>
    simp only
    split
    · split
      · rw [emit_toBytes, toBytes_with_u8]
      · rfl
    · rw [startByte_toBytes, emit_toBytes, toBytes_with_u8]

theorem step_toBytes (s : St String) (b : UInt8) : toBytes (step s b) = step (toBytes s) b := by
  unfold step
  rw [toBytes_pct]
  cases s.pct with
  | none => exact plain_toBytes s b
  | pct =>
    simp only
    cases hexVal? b with
    | some x => rfl
    | none => rw [plain_toBytes, lit_toBytes, toBytes_with_pct]
  | hex a x =>
    simp only
    cases hexVal? b with
    | some y => rw [escByte_toBytes, toBytes_with_pct]
    | none => rw [plain_toBytes, litByte_toBytes, lit_toBytes, toBytes_with_pct]

theorem finish_u8 (t : St String) :
    (match t.u8 with | .idle => t.out | .seq .. => (emit t replacement).out).toByteArray =
      (match (toBytes t).u8 with | .idle => (toBytes t).out | .seq .. => (emit (toBytes t) replacement).out) := by
  rw [toBytes_u8]
  cases t.u8 with
  | idle => rfl
  | seq _ _ _ _ => exact congrArg St.out (emit_toBytes t replacement)

theorem finish_toBytes (s : St String) : (finish s).toByteArray = finish (toBytes s) := by
  unfold finish
  rw [toBytes_pct]
  cases s.pct with
  | none => exact finish_u8 s
  | pct => simp only; rw [← toBytes_with_pct, ← lit_toBytes]; exact finish_u8 _
  | hex a x => simp only; rw [← toBytes_with_pct, ← lit_toBytes, ← litByte_toBytes]; exact finish_u8 _

theorem foldl_toBytes : ∀ (l : Bytes) (s : St String), toBytes (l.foldl step s) = l.foldl step (toBytes s) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons c l ih => intro s; rw [List.foldl_cons, List.foldl_cons, ih, step_toBytes]

/-! ## Runs of plain ASCII -/

theorem step_plain (s : St ByteArray) (c : UInt8) (hp : s.pct = .none) (hu : s.u8 = .idle)
    (hc : special c = false) : step s c = { s with out := s.out.push c } := by
  have hlt : c < 0x80 := by
    simp only [special, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    exact UInt8.not_le.mp hc.1.1
  have hpct : (c == Byte.PERCENT) = false := by simp [special] at hc; simpa using hc.1.2
  have hplus : (c == Byte.PLUS) = false := by simp [special] at hc; simpa using hc.2
  obtain ⟨out, p, u⟩ := s
  simp only at hp hu; subst hp; subst hu
  simp only [step, plain, hpct, litByte, hplus, lit, emit, Sink.push, pushUtf8, Bool.false_eq_true, ↓reduceIte]
  have hv := ascii_val c hlt
  have h127 : c.toNat ≤ 127 := by have := UInt8.lt_iff_toNat_lt.mp hlt; simp at this; omega
  simp only [hv, h127, ↓reduceIte]
  simp [UInt8.ofNat_toNat]

theorem foldl_plain : ∀ (l : Bytes) (s : St ByteArray), s.pct = .none → s.u8 = .idle →
    (∀ x ∈ l, special x = false) → l.foldl step s = { s with out := s.out ++ ⟨l.toArray⟩ } := by
  intro l
  induction l with
  | nil => intro s _ _ _; simp
  | cons c l ih =>
    intro s hp hu hl
    rw [List.foldl_cons, step_plain s c hp hu (hl c (by simp)),
      ih { s with out := s.out.push c } hp hu (fun x hx => hl x (by simp [hx]))]
    congr 1
    apply ByteArray.ext_toList; simp [ByteArray.data_append]

theorem plainSpan_le (s : St ByteArray) (b : ByteArray) (i stop : Nat) : plainSpan s b i stop ≤ stop - i := by
  unfold plainSpan; split
  · rcases scanUntil_le b special stop _ i rfl with h | h <;> omega
  · exact Nat.zero_le _

theorem plainBulk_eq (s : St ByteArray) (b : ByteArray) (i stop : Nat) :
    plainBulk s b i (plainSpan s b i stop) = ((b.data.toList.drop i).take (plainSpan s b i stop)).foldl step s := by
  unfold plainBulk
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    unfold plainSpan at h ⊢
    split at h
    · rename_i hp hu
      have hne := scanUntil_ne b special stop _ i rfl
      rcases scanUntil_le b special stop _ i rfl with hr | hr
      · omega
      · have hge := scanUntil_ge b special stop _ i rfl
        rw [foldl_plain _ s hp hu hne, copySlice_end]
        congr 1
        apply ByteArray.ext_toList
        simp only [ByteArray.data_append, Array.toList_append, extract_toList]
    · exact absurd rfl h

end Unquote

open Unquote in
/-- The decoder as compiled: UTF-8 bytes, with plain ASCII runs copied at once. -/
def unquotePlusLatin1Bytes (raw : ByteArray) : ByteArray :=
  finish (bytesFoldRun step plainSpan plainBulk (fun _ => false) raw raw.size 0
    ({ out := ByteArray.emptyWithCapacity raw.size } : St ByteArray))

open Unquote in
theorem unquotePlusLatin1Bytes_eq (raw : ByteArray) :
    unquotePlusLatin1Bytes raw = (unquotePlusLatin1 raw).toByteArray := by
  unfold unquotePlusLatin1Bytes unquotePlusLatin1
  rw [bytesFoldRun_eq step plainSpan plainBulk (fun _ => false) (fun _ _ h => by cases h) plainSpan_le
    plainBulk_eq raw raw.size _ 0 _ rfl, bytesFold_full, finish_toBytes, foldl_toBytes]
  rfl

open Unquote in
/-- A field with no `%`, `+` or byte `≥ 0x80` decodes to itself. -/
theorem unquotePlusLatin1_plain (raw : ByteArray) (h : scanUntil raw special raw.size 0 = raw.size) :
    (unquotePlusLatin1 raw).toByteArray = raw := by
  have hne := scanUntil_ne raw special raw.size _ 0 rfl
  rw [h, Nat.sub_zero, List.drop_zero, List.take_of_length_le (by simp [Array.length_toList])] at hne
  unfold unquotePlusLatin1
  rw [finish_toBytes, foldl_toBytes, foldl_plain _ _ rfl rfl hne]
  apply ByteArray.ext_toList
  simp [toBytes, finish]

/-- `unquotePlusLatin1`, run fast: a plain field is its own bytes, any other
is decoded with runs copied at once; either way the bytes are valid UTF-8
because they are the specification's string's bytes. -/
def unquotePlusLatin1Fast (raw : ByteArray) : String :=
  if h : scanUntil raw Unquote.special raw.size 0 = raw.size then
    String.ofByteArray raw (by rw [← unquotePlusLatin1_plain raw h]; exact (unquotePlusLatin1 raw).isValidUTF8)
  else
    String.ofByteArray (unquotePlusLatin1Bytes raw)
      (by rw [unquotePlusLatin1Bytes_eq]; exact (unquotePlusLatin1 raw).isValidUTF8)

@[csimp] theorem unquotePlusLatin1_eq_fast : @unquotePlusLatin1 = @unquotePlusLatin1Fast := by
  funext raw
  apply String.toByteArray_inj.mp
  unfold unquotePlusLatin1Fast
  split
  · rename_i h; exact (unquotePlusLatin1_plain raw h)
  · exact (unquotePlusLatin1Bytes_eq raw).symm

end LeanMultipart
