import LeanMultipart.RepoImpl.Multipart
import LeanMultipart.Proofs.Querystring

/-!
# The multipart state machine: chunking and totality

* `Mp.feedT_append`: feeding chunks one after another is feeding their
  concatenation, `maxSize` truncation included. Hence `Mp.parse_chunks`: the
  streaming parser fed any chunking gives the same result (parts, part in
  progress, end flag, error, byte count) as the whole-buffer parser.
* `Mp.parse_total`: the parser processes `min(len, maxSize)` bytes, and an
  error's offset is one of them.
-/

namespace LeanMultipart
namespace Mp

theorem feed_append (cx : Ctx) (s : MState) (a b : Bytes) :
    feed cx s (a ++ b) = feed cx (feed cx s a) b := by
  simp [feed, List.foldl_append]

@[simp] theorem step_pos (cx : Ctx) (s : MState) (c : UInt8) :
    (step cx s c).pos = s.pos + 1 := by
  unfold step
  cases s.phase <;>
    simp only [sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart,
      finishPart] <;> (repeat' split) <;> rfl

theorem feed_pos (cx : Ctx) (s : MState) (l : Bytes) :
    (feed cx s l).pos = s.pos + l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [feed, List.foldl_cons] at *; rw [ih]; simp; omega

theorem feedT_append (cx : Ctx) (s : MState) (a b : Bytes) :
    feedT cx (feedT cx s a) b = feedT cx s (a ++ b) := by
  unfold feedT room
  cases hm : cx.cfg.maxSize with
  | none =>
    dsimp only
    rw [List.take_of_length_le (Nat.le_refl b.length),
      List.take_of_length_le (Nat.le_refl (a ++ b).length), feed_append,
      List.take_of_length_le (Nat.le_refl a.length)]
  | some m =>
    rw [feed_pos, Qs.take_min_length, Qs.take_min_length, List.length_take, Qs.take_min_length,
      ← feed_append, List.take_append]
    by_cases h : a.length ≤ m - s.pos
    · rw [List.take_of_length_le (l := a) h, Nat.min_eq_right h]
      congr 3; omega
    · rw [Nat.min_eq_left (by omega : m - s.pos ≤ a.length),
        show m - (s.pos + (m - s.pos)) = 0 by omega, show m - s.pos - a.length = 0 by omega]

theorem feedChunks_eq (cx : Ctx) (s : MState) (cs : List Bytes) :
    feedChunks cx s cs = feedT cx s cs.flatten := by
  induction cs generalizing s with
  | nil => simp only [feedChunks, feedT, room]; split <;> simp [feed]
  | cons c cs ih => simp only [feedChunks, ih, feedT_append, List.flatten_cons]

theorem feedA_eq (cx : Ctx) (s : MState) (b : ByteArray) : feedA cx s b = feedT cx s b.data.toList := by
  have hsz : b.size = b.data.toList.length := (Array.length_toList).symm
  unfold feedA feedT feed
  rw [← Array.foldl_toList, Array.toList_extract, hsz]
  simp only [List.extract, Nat.sub_zero, List.drop_zero]

theorem parse_eq (cx : Ctx) (b : ByteArray) : parse cx b = parseL cx b.data.toList := by
  simp [parse, parseL, feedA_eq]

/-- Streaming equals whole-buffer: any chunking of the input gives the same
result. -/
theorem parse_chunks (cx : Ctx) (cs : List Bytes) :
    result (feedChunks cx {} cs) = parseL cx cs.flatten := by
  rw [feedChunks_eq]; rfl

/-- The invariant behind error localisation. -/
def ErrInv (s : MState) : Prop := ∀ e, s.phase = .failed e → e.offset < s.pos

theorem step_errInv (cx : Ctx) (s : MState) (c : UInt8) (h : ErrInv s) :
    ErrInv (step cx s c) := by
  unfold ErrInv step
  cases hp : s.phase with
  | failed e0 => have := h e0 hp; simp only [hp]; intro e he; cases he; omega
  | _ =>
    simp only [sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart,
      finishPart]
    repeat' split
    all_goals
      intro e he
      simp at he
      try subst he
      try simp
      try simp_all

theorem feed_errInv (cx : Ctx) (s : MState) (l : Bytes) (h : ErrInv s) : ErrInv (feed cx s l) := by
  induction l generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_errInv cx s c h)

/-- Totality: the parser consumes exactly `min(len, maxSize)` bytes, and an
error's offset is one of them. -/
theorem parse_total (cx : Ctx) (l : Bytes) :
    (parseL cx l).processed = room cx {} l.length ∧
    ∀ e, (parseL cx l).error = some e → e.offset < (parseL cx l).processed := by
  refine ⟨?_, ?_⟩
  · simp only [parseL, result, feedT, feed_pos, List.length_take]
    unfold room; split <;> simp <;> omega
  · intro e he
    simp only [parseL, result] at he ⊢
    split at he
    · rename_i e' hph; cases he
      exact feed_errInv cx {} _ (fun e h => by simp at h) e hph
    · cases he

end Mp
end LeanMultipart
