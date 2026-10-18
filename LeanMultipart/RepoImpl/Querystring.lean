import LeanMultipart.DataTypes.Querystring
import LeanMultipart.Theory.Machine
import LeanMultipart.RepoImpl.Percent

/-!
# The querystring state machine

Upstream's `QuerystringParser`, one byte at a time. `step` is the whole
machine; feeding a chunk is `List.foldl step`, so feeding chunks one after
another is feeding their concatenation (`Qs.feed_append` in
`Proofs/Querystring.lean`). The callback-style parser `QuerystringParser` threads the
same states and derives upstream's callbacks from each transition.

Semantics, as upstream: fields are separated by `&` only (`;` is data,
`tests/test_multipart.py::test_semicolon_is_data_not_a_field_separator`);
empty segments are skipped; a field's name runs to the first `=`, its value
from there to the next `&`; a field with no `=` has an empty value. In
strict mode a second consecutive `&` and a field without `=` that is followed
by `&` are errors.

`maxSize` truncates the input, as upstream's `max_size` does.
-/

namespace LeanMultipart
namespace Qs

/-- Close the current field. -/
def finishField (s : QsState) : QsState :=
  { s with fields := s.fields.push (s.name, s.value), name := ByteArray.empty, value := ByteArray.empty }

/-- A byte of a field name (or the `=` / `&` that ends it). `p` is the
byte's offset. -/
def nameByte (cfg : QsConfig) (s : QsState) (c : UInt8) : QsState :=
  if c == Byte.EQ then { s with phase := .fieldData }
  else if c == Byte.AMP then
    if cfg.strictParsing then { s with phase := .failed ⟨.missingEquals, s.nameStart⟩ }
    else { finishField s with phase := .beforeField true }
  else { s with phase := .fieldName, name := s.name.push c }

/-- The transition function. Every byte advances `pos`. -/
def step (cfg : QsConfig) (s : QsState) (c : UInt8) : QsState :=
  let p := s.pos
  let s := { s with pos := p + 1 }
  match s.phase with
  | .failed _ => s
  | .beforeField fs =>
    if c == Byte.AMP then
      if fs then
        if cfg.strictParsing then { s with phase := .failed ⟨.duplicateAmpersand, p⟩ } else s
      else { s with phase := .beforeField true }
    else nameByte cfg { s with nameStart := p, name := ByteArray.empty, value := ByteArray.empty } c
  | .fieldName => nameByte cfg s c
  | .fieldData =>
    if c == Byte.AMP then { finishField s with phase := .beforeField true }
    else { s with value := s.value.push c }

/-! ## Runs of a field's name or value

In a field's name every byte but `=` and `&` is appended to the name; in
its value every byte but `&` is appended to the value. `fieldSpan` finds
such a run and `fieldBulk` appends it with one copy; `fieldBulk_le` proves
that is what `step` does byte by byte, so `feedA` may take the shortcut. -/

/-- The phases in which a run is taken. -/
def InRun (s : QsState) : Prop := s.phase = .fieldName ∨ s.phase = .fieldData

/-- The bytes that end a run. -/
def runEnds (s : QsState) (c : UInt8) : Bool := c == Byte.AMP || (s.phase == .fieldName && c == Byte.EQ)

/-- Append bytes to the name (in a name) or the value. -/
def runAppend (s : QsState) (l : Bytes) : QsState :=
  if s.phase = .fieldName then { s with pos := s.pos + l.length, name := s.name ++ ⟨l.toArray⟩ }
  else { s with pos := s.pos + l.length, value := s.value ++ ⟨l.toArray⟩ }

theorem runAppend_phase (s : QsState) (l : Bytes) : (runAppend s l).phase = s.phase := by
  unfold runAppend; split <;> rfl

theorem runAppend_fields (s : QsState) (l : Bytes) : (runAppend s l).fields = s.fields := by
  unfold runAppend; split <;> rfl

theorem runAppend_size (s : QsState) (l : Bytes) :
    (runAppend s l).name.size + (runAppend s l).value.size = s.name.size + s.value.size + l.length := by
  have hm : (ByteArray.mk l.toArray).size = l.length := by
    show l.toArray.size = l.length; simp
  unfold runAppend; split <;> simp only [ByteArray.size_append, hm] <;> omega

theorem step_run (cfg : QsConfig) (s : QsState) (c : UInt8) (hs : InRun s) (hc : runEnds s c = false) :
    step cfg s c = runAppend s [c] := by
  obtain ⟨ph, pos, ns, n, v, fs⟩ := s
  unfold InRun at hs; simp only at hs
  rcases hs with hs | hs <;> subst hs <;> simp [runEnds] at hc
  · simp [step, nameByte, hc, runAppend]
    apply ByteArray.ext; simp [ByteArray.data_append]
  · simp [step, hc, runAppend]
    apply ByteArray.ext; simp [ByteArray.data_append]

theorem runAppend_append (s : QsState) (l l' : Bytes) :
    runAppend (runAppend s l) l' = runAppend s (l ++ l') := by
  unfold runAppend
  by_cases h : s.phase = .fieldName <;> simp only [h, ↓reduceIte, List.length_append] <;>
    (congr 1 <;> first | omega | (apply ByteArray.ext; simp [ByteArray.data_append]))

theorem foldl_run (cfg : QsConfig) : ∀ (l : Bytes) (s : QsState), InRun s →
    (∀ x ∈ l, runEnds s x = false) → l.foldl (step cfg) s = runAppend s l := by
  intro l
  induction l with
  | nil => intro s _ _; unfold runAppend; split <;> simp
  | cons c l ih =>
    intro s hs hl
    have hph := runAppend_phase s [c]
    have hs' : InRun (runAppend s [c]) := by unfold InRun at *; rw [hph]; exact hs
    rw [List.foldl_cons, step_run cfg s c hs (hl c (by simp)),
      ih _ hs' (fun x hx => by unfold runEnds at *; rw [hph]; exact hl x (by simp [hx])),
      runAppend_append]
    rfl

/-- The length of the run at `i`, before `stop` (0 if none). -/
def fieldSpan (s : QsState) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.phase with
  | .fieldName => scanUntil b (fun c => c == Byte.AMP || c == Byte.EQ) stop i - i
  | .fieldData => scanFor b Byte.AMP stop i - i
  | _ => 0

/-- Append the `n` bytes at `i` to the name or the value. -/
def fieldBulk (s : QsState) (b : ByteArray) (i n : Nat) : QsState :=
  if n = 0 then s
  else match s.phase with
    | .fieldName => { s with pos := s.pos + n, name := b.copySlice i s.name s.name.size n (s.name.size == 0) }
    | _ => { s with pos := s.pos + n, value := b.copySlice i s.value s.value.size n (s.value.size == 0) }

theorem fieldSpan_le (s : QsState) (b : ByteArray) (i stop : Nat) : fieldSpan s b i stop ≤ stop - i := by
  unfold fieldSpan; split
  · rcases scanUntil_le b (fun c => c == Byte.AMP || c == Byte.EQ) stop _ i rfl with h | h <;> omega
  · rcases scanFor_le b Byte.AMP stop _ i rfl with h | h <;> omega
  · exact Nat.zero_le _

theorem fieldSpan_run (s : QsState) (b : ByteArray) (i stop : Nat) (h : fieldSpan s b i stop ≠ 0) : InRun s := by
  unfold fieldSpan at h; unfold InRun; split at h
  · left; assumption
  · right; assumption
  · exact absurd rfl h

theorem fieldSpan_ne (s : QsState) (b : ByteArray) (i stop : Nat) :
    ∀ x ∈ (b.data.toList.drop i).take (fieldSpan s b i stop), runEnds s x = false := by
  intro x hx
  unfold fieldSpan at hx; unfold runEnds; split at hx
  · rename_i hp
    have := scanUntil_ne b (fun c => c == Byte.AMP || c == Byte.EQ) stop _ i rfl x hx
    rw [hp]; simp only [Bool.or_eq_false_iff] at this; simp [this.1, this.2]
  · rename_i hp
    have := scanFor_ne b Byte.AMP stop _ i rfl x hx
    rw [hp]; simp [this]
  · simp at hx

theorem fieldSpan_size (s : QsState) (b : ByteArray) (i stop : Nat) :
    i + fieldSpan s b i stop ≤ b.size ∨ fieldSpan s b i stop = 0 := by
  unfold fieldSpan; split
  · rcases scanUntil_le b (fun c => c == Byte.AMP || c == Byte.EQ) stop _ i rfl with h | h <;> omega
  · rcases scanFor_le b Byte.AMP stop _ i rfl with h | h <;> omega
  · exact Or.inr rfl

/-- Any prefix of a run, appended at once, is what `step` does. -/
theorem fieldBulk_le (cfg : QsConfig) (s : QsState) (b : ByteArray) (i stop k : Nat) (hk : k ≤ fieldSpan s b i stop) :
    fieldBulk s b i k = ((b.data.toList.drop i).take k).foldl (step cfg) s := by
  unfold fieldBulk
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    have hrun := fieldSpan_run s b i stop (by omega)
    have hne : ∀ x ∈ (b.data.toList.drop i).take k, runEnds s x = false := fun x hx =>
      fieldSpan_ne s b i stop x (List.take_subset_take_left _ hk hx)
    have hlen : ((b.data.toList.drop i).take k).length = k := by
      rcases fieldSpan_size s b i stop with hs | hs
      · simp [Array.length_toList]; omega
      · omega
    rw [foldl_run cfg _ s hrun hne]
    unfold runAppend
    rw [hlen]
    rcases hrun with hp | hp
    · simp only [hp, ↓reduceIte, copySlice_end]
      congr 1
      apply ByteArray.ext_toList
      simp only [ByteArray.data_append, Array.toList_append, extract_toList]
    · simp only [hp, reduceCtorEq, ↓reduceIte, copySlice_end]
      congr 1
      apply ByteArray.ext_toList
      simp only [ByteArray.data_append, Array.toList_append, extract_toList]

/-- The machine: `step`, the byte counter, and the `maxSize` limit, with the
shortcut for runs of a name or value. The general chunking theorems of
`Theory/Machine.lean` apply to it. -/
def machine (cfg : QsConfig) : Machine QsState :=
  { step := step cfg, pos := QsState.pos, limit := cfg.maxSize,
    span := fieldSpan, bulk := fieldBulk, span_le := fieldSpan_le,
    bulk_eq := fun s b i stop => fieldBulk_le cfg s b i stop _ (Nat.le_refl _) }

/-- Feed bytes (no truncation). -/
def feed (cfg : QsConfig) (s : QsState) (l : Bytes) : QsState := l.foldl (step cfg) s

/-- How many more bytes `maxSize` allows. -/
def room (cfg : QsConfig) (s : QsState) (n : Nat) : Nat :=
  match cfg.maxSize with
  | none => n
  | some m => min n (m - s.pos)

/-- Feed bytes, truncated at `maxSize`. -/
def feedT (cfg : QsConfig) (s : QsState) (l : Bytes) : QsState :=
  feed cfg s (l.take (room cfg s l.length))

/-- Feeding the chunks of a list one after another, as a `QuerystringParser` does. -/
def feedChunks (cfg : QsConfig) (s : QsState) (cs : List Bytes) : QsState := (machine cfg).feedChunks s cs

/-- The number of bytes the whole-buffer parser processes. -/
def processed (cfg : QsConfig) (l : Bytes) : Nat := (feedT cfg {} l).pos

/-- End of input: close a field in progress. -/
def finish (s : QsState) : QsState :=
  match s.phase with
  | .fieldName | .fieldData => { finishField s with phase := .beforeField false }
  | _ => s

/-- The result of a finished state. -/
def result (s : QsState) : Except QsError (List QsField) :=
  match (finish s).phase with
  | .failed e => .error e
  | _ => .ok (finish s).fields.toList

/-- The whole-buffer parser, on a list. -/
def parseL (cfg : QsConfig) (l : Bytes) : Except QsError (List QsField) :=
  result (feedT cfg {} l)

/-- Feed a byte array, truncated at `maxSize`, as an array fold (no
intermediate list). Equal to `feedT` on the list (`Qs.feedA_eq`). -/
def feedA (cfg : QsConfig) (s : QsState) (b : ByteArray) : QsState :=
  (machine cfg).feedA s b

/-- The whole-buffer parser. Equal to `parseL` on the bytes (`Qs.parse_eq`). -/
def parse (cfg : QsConfig) (b : ByteArray) : Except QsError (List QsField) :=
  result (feedA cfg {} b)

end Qs

/-! ## urlencode / urldecode -/

/-- One `name=value` pair, `quote_plus`-encoded. -/
def encodePairL (p : Bytes × Bytes) : Bytes := quotePlusL p.1 ++ [Byte.EQ] ++ quotePlusL p.2

/-- `urllib.parse.urlencode` on byte pairs: pairs joined by `&`. -/
def urlencodeL : List (Bytes × Bytes) → Bytes
  | [] => []
  | p :: ps => encodePairL p ++ ps.flatMap (fun q => [Byte.AMP] ++ encodePairL q)

/-- Decode a body: the non-strict parser, then `unquote_plus` on each name
and value. Total: the non-strict parser has no error case. -/
def urldecodeL (l : Bytes) : List (Bytes × Bytes) :=
  match Qs.parseL {} l with
  | .ok fs => fs.map (fun f => (unquotePlusL f.1.data.toList, unquotePlusL f.2.data.toList))
  | .error _ => []

/-- `urlencode` on byte arrays. -/
def urlencodeB (ps : List (ByteArray × ByteArray)) : ByteArray :=
  ⟨(urlencodeL (ps.map fun p => (p.1.data.toList, p.2.data.toList))).toArray⟩

/-- `urldecode` on byte arrays. -/
def urldecodeB (b : ByteArray) : List (ByteArray × ByteArray) :=
  (urldecodeL b.data.toList).map fun p => (⟨p.1.toArray⟩, ⟨p.2.toArray⟩)

/-- `urlencode` on strings: UTF-8, then `quote_plus`. The result is ASCII. -/
def urlencodeStr (ps : List (String × String)) : String :=
  latin1Decode (urlencodeB (ps.map fun p => (p.1.toUTF8, p.2.toUTF8)))

/-- `urldecode` on strings: each name and value is UTF-8 if valid, else
Latin-1. -/
def urldecodeStr (s : String) : List (String × String) :=
  (urldecodeB s.toUTF8).map fun p => (decodeUtf8OrLatin1 p.1, decodeUtf8OrLatin1 p.2)

end LeanMultipart
