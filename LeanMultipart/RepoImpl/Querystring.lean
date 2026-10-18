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

/-! ## Runs of field data

In a field's value every byte but `&` is appended. `valueSpan` finds such a
run and `valueBulk` appends it with one copy; `valueBulk_le` proves that is
what `step` does byte by byte, so `feedA` may take the shortcut. -/

/-- The length of the run of value bytes at `i`, before `stop` (0 if none). -/
def valueSpan (s : QsState) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.phase with
  | .fieldData => scanFor b Byte.AMP stop i - i
  | _ => 0

/-- Append the `n` bytes at `i` to the value. -/
def valueBulk (s : QsState) (b : ByteArray) (i n : Nat) : QsState :=
  if n = 0 then s else { s with pos := s.pos + n, value := b.copySlice i s.value s.value.size n false }

theorem step_value (cfg : QsConfig) (s : QsState) (c : UInt8) (hs : s.phase = .fieldData)
    (hc : c ≠ Byte.AMP) : step cfg s c = { s with pos := s.pos + 1, value := s.value.push c } := by
  obtain ⟨ph, pos, ns, n, v, fs⟩ := s
  simp only at hs; subst hs
  simp [step, hc]

theorem foldl_value (cfg : QsConfig) : ∀ (l : Bytes) (s : QsState), s.phase = .fieldData →
    (∀ x ∈ l, x ≠ Byte.AMP) →
    l.foldl (step cfg) s = { s with pos := s.pos + l.length, value := s.value ++ ⟨l.toArray⟩ } := by
  intro l
  induction l with
  | nil => intro s _ _; simp
  | cons c l ih =>
    intro s hs hl
    rw [List.foldl_cons, step_value cfg s c hs (hl c (by simp)),
      ih { s with pos := s.pos + 1, value := s.value.push c } hs (fun x hx => hl x (by simp [hx]))]
    simp only [List.length_cons]
    congr 1
    · omega
    · apply ByteArray.ext_toList; simp [ByteArray.data_append]

theorem valueSpan_le (s : QsState) (b : ByteArray) (i stop : Nat) : valueSpan s b i stop ≤ stop - i := by
  unfold valueSpan; split
  · rcases scanFor_le b Byte.AMP stop _ i rfl with h | h <;> omega
  · exact Nat.zero_le _

theorem valueSpan_phase (s : QsState) (b : ByteArray) (i stop : Nat) (h : valueSpan s b i stop ≠ 0) :
    s.phase = .fieldData := by
  unfold valueSpan at h; split at h
  · assumption
  · exact absurd rfl h

theorem valueSpan_ne (s : QsState) (b : ByteArray) (i stop : Nat) :
    ∀ x ∈ (b.data.toList.drop i).take (valueSpan s b i stop), x ≠ Byte.AMP := by
  unfold valueSpan; split
  · exact scanFor_ne b Byte.AMP stop _ i rfl
  · simp

theorem valueSpan_size (s : QsState) (b : ByteArray) (i stop : Nat) :
    i + valueSpan s b i stop ≤ b.size ∨ valueSpan s b i stop = 0 := by
  unfold valueSpan; split
  · rcases scanFor_le b Byte.AMP stop _ i rfl with h | h <;> omega
  · exact Or.inr rfl

/-- Any prefix of a run, appended at once, is what `step` does. -/
theorem valueBulk_le (cfg : QsConfig) (s : QsState) (b : ByteArray) (i stop k : Nat) (hk : k ≤ valueSpan s b i stop) :
    valueBulk s b i k = ((b.data.toList.drop i).take k).foldl (step cfg) s := by
  unfold valueBulk
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    have hph := valueSpan_phase s b i stop (by omega)
    have hne : ∀ x ∈ (b.data.toList.drop i).take k, x ≠ Byte.AMP := fun x hx =>
      valueSpan_ne s b i stop x (List.take_subset_take_left _ hk hx)
    have hlen : ((b.data.toList.drop i).take k).length = k := by
      rcases valueSpan_size s b i stop with hs | hs
      · simp [Array.length_toList]; omega
      · omega
    rw [foldl_value cfg _ s hph hne, hlen, copySlice_end]
    congr 1
    apply ByteArray.ext_toList
    simp only [ByteArray.data_append, Array.toList_append, extract_toList]

/-- The machine: `step`, the byte counter, and the `maxSize` limit, with the
shortcut for runs of field data. The general chunking theorems of
`Theory/Machine.lean` apply to it. -/
def machine (cfg : QsConfig) : Machine QsState :=
  { step := step cfg, pos := QsState.pos, limit := cfg.maxSize,
    span := valueSpan, bulk := valueBulk, span_le := valueSpan_le,
    bulk_eq := fun s b i stop => valueBulk_le cfg s b i stop _ (Nat.le_refl _) }

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
