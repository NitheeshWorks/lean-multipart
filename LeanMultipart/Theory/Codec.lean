import LeanMultipart.Theory.Machine

/-!
# Codecs: printers read back by machines

A *codec* here is a printer built from byte strings by concatenation,
`flatMap` and separators, and a byte machine that reads it. The round trip
is proved with one judgement,

  `Reads M P w Q`: from any state satisfying `P`, feeding `w` reaches a state
  satisfying `Q`,

and one lemma per way of building a printer:

| printer | lemma |
|---|---|
| `[]` | `Reads.nil` |
| `w ++ v` | `Reads.append` |
| `xs.flatMap enc` | `Reads.flatMap` |
| `enc x₀ ++ xs.flatMap (sep ++ enc ·)` | `Reads.sepBy` |
| weaken / strengthen | `Reads.mono` |

The percent codec, the urlencoded codec and the multipart codec are
instances: each proves a `Reads` fact for one token (a byte, a pair, a
header line, a part) and assembles the message with these lemmas.
Because a `Reads` fact holds from *every* state satisfying `P`, it holds on
any continuation of the buffer, which is the `_ext` form.
-/

namespace LeanMultipart

variable {σ : Type} (M : Machine σ)

/-- From any state satisfying `P`, feeding `w` reaches a state satisfying `Q`. -/
def Reads (P : σ → Prop) (w : Bytes) (Q : σ → Prop) : Prop := ∀ s, P s → Q (M.feed s w)

namespace Reads

variable {M}

theorem nil {P : σ → Prop} : Reads M P [] P := fun _ h => h

theorem append {P Q R : σ → Prop} {w v : Bytes} (h₁ : Reads M P w Q) (h₂ : Reads M Q v R) :
    Reads M P (w ++ v) R := by
  intro s hs; rw [M.feed_append]; exact h₂ _ (h₁ s hs)

theorem mono {P P' Q Q' : σ → Prop} {w : Bytes} (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (h : Reads M P w Q) : Reads M P' w Q' := fun s hs => hQ _ (h s (hP s hs))

/-- Many tokens: an invariant indexed by what has been read. -/
theorem flatMap {α : Type} {I : List α → σ → Prop} (enc : α → Bytes) (xs : List α)
    (h : ∀ acc x, x ∈ xs → Reads M (I acc) (enc x) (I (acc ++ [x]))) :
    ∀ acc, Reads M (I acc) (xs.flatMap enc) (I (acc ++ xs)) := by
  induction xs with
  | nil => intro acc; simpa using (nil : Reads M (I acc) [] (I acc))
  | cons x xs ih =>
    intro acc
    rw [List.flatMap_cons]
    have := append (h acc x (by simp)) (ih (fun a y hy => h a y (by simp [hy])) (acc ++ [x]))
    simpa using this

/-- Tokens separated by `sep`: after each token the machine is in `J`, and
the separator brings it back to `I`. -/
theorem sepBy {α : Type} {I J : List α → σ → Prop} (enc : α → Bytes) (sep : Bytes)
    (x₀ : α) (xs : List α)
    (hx : ∀ acc x, x ∈ x₀ :: xs → Reads M (I acc) (enc x) (J (acc ++ [x])))
    (hs : ∀ acc, Reads M (J acc) sep (I acc)) :
    ∀ acc, Reads M (I acc) (enc x₀ ++ xs.flatMap (fun x => sep ++ enc x)) (J (acc ++ x₀ :: xs)) := by
  induction xs generalizing x₀ with
  | nil => intro acc; simpa using hx acc x₀ (by simp)
  | cons x xs ih =>
    intro acc
    have e : enc x₀ ++ (x :: xs).flatMap (fun x => sep ++ enc x) =
        (enc x₀ ++ sep) ++ (enc x ++ xs.flatMap (fun x => sep ++ enc x)) := by simp
    rw [e]
    have := append (append (hx acc x₀ (by simp)) (hs (acc ++ [x₀])))
      (ih x (fun a y hy => hx a y (List.mem_cons_of_mem _ hy)) (acc ++ [x₀]))
    simpa using this

/-- `xs.flatMap (a ++ f ·) ++ a = a ++ xs.flatMap (f · ++ a)`: moving a
separator from before each token to after it. -/
theorem flatMap_rotate {α : Type} (a : Bytes) (f : α → Bytes) (xs : List α) :
    xs.flatMap (fun x => a ++ f x) ++ a = a ++ xs.flatMap (fun x => f x ++ a) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.append_assoc, ih]

end Reads
end LeanMultipart
