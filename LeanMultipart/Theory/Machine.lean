import LeanMultipart.DataTypes.Bytes

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

/-- Feed a byte array, truncated at the limit, as an array fold. -/
def feedA (s : σ) (b : ByteArray) : σ := (b.data.extract 0 (M.room s b.size)).foldl M.step s

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

theorem feedT_append (h : M.Counts) (s : σ) (a b : Bytes) :
    M.feedT (M.feedT s a) b = M.feedT s (a ++ b) := by
  unfold feedT room
  cases hm : M.limit with
  | none =>
    dsimp only
    rw [List.take_of_length_le (Nat.le_refl b.length),
      List.take_of_length_le (Nat.le_refl (a ++ b).length), feed_append,
      List.take_of_length_le (Nat.le_refl a.length)]
  | some m =>
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
theorem feedChunks_eq (h : M.Counts) (s : σ) (cs : List Bytes) :
    M.feedChunks s cs = M.feedT s cs.flatten := by
  induction cs generalizing s with
  | nil => exact (M.feedT_nil s).symm
  | cons c cs ih => simp only [feedChunks, ih, M.feedT_append h, List.flatten_cons]

theorem feedA_eq (s : σ) (b : ByteArray) : M.feedA s b = M.feedT s b.data.toList := by
  have hsz : b.size = b.data.toList.length := (Array.length_toList).symm
  unfold feedA feedT feed
  rw [← Array.foldl_toList, Array.toList_extract, hsz]
  simp only [List.extract, Nat.sub_zero, List.drop_zero]

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
