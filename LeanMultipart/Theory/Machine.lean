import LeanMultipart.DataTypes.Bytes
import LeanMultipart.Theory.BytesFacts

/-!
# Byte machines

Every parser in this library is a *byte machine*: a state, a transition
function on one byte, a byte counter, and an optional input limit
(upstream's `max_size`). Feeding input is a left fold. This file proves,
once for every machine:

* `feed_append`: feeding `a` then `b` is feeding `a ++ b`;
* `feedT_append`: the same with the input limit applied to each chunk;
* `feedChunks_eq`: feeding any chunking is feeding the concatenation;
* `feedA_eq`: the array fold the implementation runs equals the list fold;
* `feed_forget`: forgetting buffers the transition never reads commutes with
  feeding, which is how the streaming parsers, which drop what they have
  reported, are related to the whole-buffer parsers.

The querystring and multipart parsers are instances (`Qs.machine`,
`Mp.machine`), so their chunking theorems are one line each.
-/

namespace LeanMultipart

/-- Fold `f` over the bytes of `b` from index `i` to `stop`, reading the
packed byte array directly (no conversion to an array of boxed bytes). -/
def bytesFold {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (stop : Nat) (i : Nat) (s : τ) : τ :=
  if h : i < stop ∧ i < b.size then bytesFold f b stop (i + 1) (f s b[i]) else s
termination_by stop - i

theorem bytesFold_eq {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (stop : Nat) : ∀ (n i : Nat) (s : τ),
    stop - i = n → bytesFold f b stop i s = ((b.data.toList.drop i).take (stop - i)).foldl f s := by
  intro n
  induction n with
  | zero =>
    intro i s hn
    unfold bytesFold
    split
    · omega
    · rw [show stop - i = 0 by omega]; simp
  | succ n ih =>
    intro i s hn
    unfold bytesFold
    split
    · rename_i h
      rw [ih (i + 1) _ (by omega)]
      have hl : i < b.data.toList.length := by rw [Array.length_toList]; exact h.2
      rw [List.drop_eq_getElem_cons hl, show stop - i = (stop - (i + 1)) + 1 by omega, List.take_succ_cons]
      simp only [List.foldl_cons, ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    · rename_i h
      have hi : ¬ i < b.size := fun hi => h ⟨by omega, hi⟩
      have : b.data.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt hi)
      rw [this]; simp

/-- `bytesFold` from the start, up to `n` bytes, is the list fold of the first `n` bytes. -/
theorem bytesFold_take {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (n : Nat) (s : τ) :
    bytesFold f b n 0 s = (b.data.toList.take n).foldl f s := by
  rw [bytesFold_eq f b n n 0 s (by omega)]; simp

theorem bytesFold_full {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (s : τ) :
    bytesFold f b b.size 0 s = b.data.toList.foldl f s := by
  rw [bytesFold_take, List.take_of_length_le (by rw [Array.length_toList]; exact Nat.le_refl _)]

/-- A byte machine. -/
structure Machine (σ : Type) where
  step : σ → UInt8 → σ
  pos : σ → Nat
  limit : Option Nat

namespace Machine

variable {σ : Type} (M : Machine σ)

/-- Feed bytes. -/
def feed (s : σ) (l : Bytes) : σ := l.foldl M.step s

/-- How many of `n` bytes the limit allows from `s`. -/
def room (s : σ) (n : Nat) : Nat :=
  match M.limit with
  | none => n
  | some m => min n (m - M.pos s)

/-- Feed bytes, truncated at the limit. -/
def feedT (s : σ) (l : Bytes) : σ := M.feed s (l.take (M.room s l.length))

/-- Feed a byte array, truncated at the limit. -/
def feedA (s : σ) (b : ByteArray) : σ := bytesFold M.step b (M.room s b.size) 0 s

/-- Feed chunks one after another. -/
def feedChunks (s : σ) : List Bytes → σ
  | [] => s
  | c :: cs => feedChunks (M.feedT s c) cs

/-- The machine counts every byte. -/
def Counts : Prop := ∀ s c, M.pos (M.step s c) = M.pos s + 1

theorem feed_append (s : σ) (a b : Bytes) : M.feed s (a ++ b) = M.feed (M.feed s a) b := by
  simp [feed, List.foldl_append]

theorem feed_pos (h : M.Counts) (s : σ) (l : Bytes) : M.pos (M.feed s l) = M.pos s + l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [feed, List.foldl_cons] at *; rw [ih, h]; simp; omega

theorem take_min_length (l : Bytes) (r : Nat) : l.take (min l.length r) = l.take r := by
  by_cases h : l.length ≤ r
  · rw [Nat.min_eq_left h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]
  · rw [Nat.min_eq_right (by omega)]

/-- The chunking theorems need the byte counter only when there is an input
limit. -/
def Chunkable : Prop := M.limit = none ∨ M.Counts

theorem chunkable_of_counts (h : M.Counts) : M.Chunkable := Or.inr h

theorem feedT_append (hc : M.Chunkable) (s : σ) (a b : Bytes) :
    M.feedT (M.feedT s a) b = M.feedT s (a ++ b) := by
  unfold feedT room
  cases hm : M.limit with
  | none =>
    dsimp only
    rw [List.take_of_length_le (Nat.le_refl b.length),
      List.take_of_length_le (Nat.le_refl (a ++ b).length), feed_append,
      List.take_of_length_le (Nat.le_refl a.length)]
  | some m =>
    have h : M.Counts := hc.resolve_left (by simp [hm])
    rw [feed_pos M h, take_min_length, take_min_length, List.length_take, take_min_length,
      ← feed_append, List.take_append]
    by_cases hl : a.length ≤ m - M.pos s
    · rw [List.take_of_length_le (l := a) hl, Nat.min_eq_right hl]
      congr 3; omega
    · rw [Nat.min_eq_left (by omega : m - M.pos s ≤ a.length),
        show m - (M.pos s + (m - M.pos s)) = 0 by omega, show m - M.pos s - a.length = 0 by omega]

theorem feedT_nil (s : σ) : M.feedT s [] = s := by
  simp only [feedT, room]; split <;> simp [feed]

/-- Feeding any chunking is feeding the concatenation. -/
theorem feedChunks_eq (h : M.Chunkable) (s : σ) (cs : List Bytes) :
    M.feedChunks s cs = M.feedT s cs.flatten := by
  induction cs generalizing s with
  | nil => exact (M.feedT_nil s).symm
  | cons c cs ih => simp only [feedChunks, ih, M.feedT_append h, List.flatten_cons]

theorem feedA_eq (s : σ) (b : ByteArray) : M.feedA s b = M.feedT s b.data.toList := by
  have hsz : b.size = b.data.toList.length := (Array.length_toList).symm
  unfold feedA feedT feed
  rw [bytesFold_take, hsz]

theorem feedA_append (h : M.Chunkable) (s : σ) (a b : ByteArray) :
    M.feedA (M.feedA s a) b = M.feedA s (a ++ b) := by
  rw [M.feedA_eq, M.feedA_eq, M.feedA_eq, M.feedT_append h, ByteArray.data_append, Array.toList_append]

theorem feedA_empty (s : σ) : M.feedA s ByteArray.empty = s := by
  rw [M.feedA_eq]; exact M.feedT_nil s

/-- Writing chunks one after another is writing their concatenation. -/
theorem feedA_chunks (h : M.Chunkable) (s : σ) (cs : List ByteArray) :
    cs.foldl M.feedA s = M.feedA s (concatChunks cs) := by
  induction cs generalizing s with
  | nil => exact (M.feedA_empty s).symm
  | cons c cs ih =>
    rw [List.foldl_cons, ih, M.feedA_append h]
    congr 1

/-! ## Stopping early

A machine whose halted states are fixed points can stop reading as soon as
it halts (a limit error, a parse error, the end of the message). -/

/-- `bytesFold`, stopping when `halted` holds. -/
def bytesFoldUntil {τ : Type} (f : τ → UInt8 → τ) (halted : τ → Bool) (b : ByteArray) (stop : Nat)
    (i : Nat) (s : τ) : τ :=
  if halted s then s
  else if h : i < stop ∧ i < b.size then bytesFoldUntil f halted b stop (i + 1) (f s b[i]) else s
termination_by stop - i

theorem bytesFoldUntil_eq {τ : Type} (f : τ → UInt8 → τ) (halted : τ → Bool)
    (hfix : ∀ s c, halted s = true → f s c = s) (b : ByteArray) (stop : Nat) :
    ∀ (n i : Nat) (s : τ), stop - i = n → bytesFoldUntil f halted b stop i s = bytesFold f b stop i s := by
  intro n
  induction n with
  | zero =>
    intro i s hn
    unfold bytesFoldUntil bytesFold
    split
    · split
      · rename_i h; omega
      · rfl
    · split
      · rename_i h; omega
      · rfl
  | succ n ih =>
    intro i s hn
    by_cases hs : halted s = true
    · -- a halted state stays put, so the full fold returns it too
      have hfold : ∀ (k j : Nat), stop - j = k → bytesFold f b stop j s = s := by
        intro k
        induction k with
        | zero =>
          intro j hj; unfold bytesFold; split
          · rename_i h; omega
          · rfl
        | succ k ihk =>
          intro j hj; unfold bytesFold; split
          · rw [hfix s _ hs]; exact ihk (j + 1) (by omega)
          · rfl
      unfold bytesFoldUntil; simp only [hs, ↓reduceIte]; exact (hfold _ i rfl).symm
    · unfold bytesFoldUntil bytesFold
      simp only [hs, Bool.false_eq_true, ↓reduceIte]
      split
      · exact ih (i + 1) _ (by omega)
      · rfl

/-- Feed a byte array, stopping when the machine halts. -/
def feedAUntil (halted : σ → Bool) (s : σ) (b : ByteArray) : σ :=
  bytesFoldUntil M.step halted b (M.room s b.size) 0 s

theorem feedAUntil_eq {halted : σ → Bool} (hfix : ∀ s c, halted s = true → M.step s c = s)
    (s : σ) (b : ByteArray) : M.feedAUntil halted s b = M.feedA s b := by
  unfold feedAUntil feedA
  exact bytesFoldUntil_eq M.step halted hfix b _ _ 0 s rfl

/-! ## Forgetting buffers -/

/-- `f` forgets only what the transition never reads: it is idempotent and
commutes with a step. -/
def Forgets (f : σ → σ) : Prop := (∀ s, f (f s) = f s) ∧ ∀ s c, f (M.step (f s) c) = f (M.step s c)

theorem feed_forget {f : σ → σ} (hf : M.Forgets f) (s : σ) (l : Bytes) :
    f (M.feed (f s) l) = f (M.feed s l) := by
  induction l generalizing s with
  | nil => exact hf.1 s
  | cons c cs ih =>
    simp only [feed, List.foldl_cons] at *
    rw [← ih (M.step (f s) c), hf.2, ih]

theorem feed_forget_congr {f : σ → σ} (hf : M.Forgets f) {s t : σ} (h : f s = f t) (l : Bytes) :
    f (M.feed s l) = f (M.feed t l) := by
  rw [← M.feed_forget hf, h, M.feed_forget hf]

/-- A fold that steps the machine, forgets some buffers, and produces
output on the side runs the machine, up to what it forgets. -/
theorem foldl_forget {τ : Type} {f : σ → σ} (hf : M.Forgets f) (stepE : σ × τ → UInt8 → σ × τ)
    (hE : ∀ s e c, f (stepE (s, e) c).1 = f (M.step s c)) (l : Bytes) :
    ∀ (s : σ) (e : τ), f (l.foldl stepE (s, e)).1 = f (M.feed s l) := by
  induction l with
  | nil => intro s e; rfl
  | cons c cs ih =>
    intro s e
    simp only [List.foldl_cons]
    generalize hq : stepE (s, e) c = q
    obtain ⟨t, e'⟩ := q
    rw [ih t e']
    have := hE s e c
    rw [hq] at this
    exact (M.feed_forget_congr hf this cs).trans (by simp [feed])

end Machine
end LeanMultipart
