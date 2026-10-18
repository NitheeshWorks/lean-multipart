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

/-- A fold from a fixed point stays there. -/
theorem bytesFold_fixed {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (stop : Nat) (s : τ)
    (hs : ∀ c, f s c = s) : ∀ (n i : Nat), stop - i = n → bytesFold f b stop i s = s := by
  intro n
  induction n with
  | zero =>
    intro j hj; unfold bytesFold; split
    · rename_i h; omega
    · rfl
  | succ k ihk =>
    intro j hj; unfold bytesFold; split
    · rw [hs]; exact ihk (j + 1) (by omega)
    · rfl

/-- Folding the next `n` bytes as a list, then the rest, is the fold. -/
theorem bytesFold_skip {τ : Type} (f : τ → UInt8 → τ) (b : ByteArray) (stop i n : Nat) (s : τ)
    (hn : n ≤ stop - i) :
    bytesFold f b stop i s = bytesFold f b stop (i + n) (((b.data.toList.drop i).take n).foldl f s) := by
  rw [bytesFold_eq f b stop _ i s rfl, bytesFold_eq f b stop _ (i + n) _ rfl, ← List.foldl_append,
    ← List.drop_drop, ← List.take_add, show n + (stop - (i + n)) = stop - i by omega]

/-- `bytesFold` with two shortcuts: it stops as soon as `halted` holds, and
where `span` says the next `n > 0` bytes can be consumed at once, `bulk`
consumes them (a run of part data, say, appended with one copy). -/
def bytesFoldRun {τ : Type} (f : τ → UInt8 → τ) (span : τ → ByteArray → Nat → Nat → Nat)
    (bulk : τ → ByteArray → Nat → Nat → τ) (halted : τ → Bool) (b : ByteArray) (stop : Nat)
    (i : Nat) (s : τ) : τ :=
  if halted s then s
  else if h : i < stop ∧ i < b.size then
    let n := span s b i stop
    if hn : n = 0 then bytesFoldRun f span bulk halted b stop (i + 1) (f s b[i])
    else bytesFoldRun f span bulk halted b stop (i + n) (bulk s b i n)
  else s
termination_by stop - i
decreasing_by all_goals omega

/-- The shortcuts are sound: halted states are fixed points, and `bulk`
does what folding `span` bytes would. -/
theorem bytesFoldRun_eq {τ : Type} (f : τ → UInt8 → τ) (span : τ → ByteArray → Nat → Nat → Nat)
    (bulk : τ → ByteArray → Nat → Nat → τ) (halted : τ → Bool)
    (hfix : ∀ s c, halted s = true → f s c = s)
    (hspan : ∀ s b i stop, span s b i stop ≤ stop - i)
    (hbulk : ∀ s b i stop, bulk s b i (span s b i stop) =
      ((b.data.toList.drop i).take (span s b i stop)).foldl f s)
    (b : ByteArray) (stop : Nat) :
    ∀ (n i : Nat) (s : τ), stop - i = n →
      bytesFoldRun f span bulk halted b stop i s = bytesFold f b stop i s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i s hn
    by_cases hs : halted s = true
    · unfold bytesFoldRun; simp only [hs, ↓reduceIte]
      exact (bytesFold_fixed f b stop s (fun c => hfix s c hs) _ i rfl).symm
    · unfold bytesFoldRun
      simp only [hs, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i h
        split
        · rw [ih (stop - (i + 1)) (by omega) (i + 1) _ rfl]
          conv => rhs; unfold bytesFold
          simp only [h, and_self, ↓reduceDIte]
        · rename_i hn0
          have hle := hspan s b i stop
          rw [ih (stop - (i + span s b i stop)) (by omega) _ _ rfl, hbulk,
            ← bytesFold_skip f b stop i _ s hle]
      · rename_i h
        unfold bytesFold; simp only [h, ↓reduceDIte]

/-- The first index from `i`, before `stop`, holding `c`; or where the
search ran out (`stop`, the end of `b`, or `i` itself). -/
def scanFor (b : ByteArray) (c : UInt8) (stop i : Nat) : Nat :=
  if h : i < stop ∧ i < b.size then (if b[i] = c then i else scanFor b c stop (i + 1)) else i
termination_by stop - i

theorem scanFor_ge (b : ByteArray) (c : UInt8) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → i ≤ scanFor b c stop i := by
  intro n
  induction n with
  | zero => intro i hn; unfold scanFor; split
            · omega
            · exact Nat.le_refl _
  | succ n ih =>
    intro i hn; unfold scanFor; split
    · split
      · exact Nat.le_refl _
      · have := ih (i + 1) (by omega); omega
    · exact Nat.le_refl _

/-- Past `i`, the search stays within `stop` and the end of `b`. -/
theorem scanFor_le (b : ByteArray) (c : UInt8) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → scanFor b c stop i = i ∨ (scanFor b c stop i ≤ stop ∧ scanFor b c stop i ≤ b.size) := by
  intro n
  induction n with
  | zero => intro i hn; unfold scanFor; split
            · omega
            · exact Or.inl rfl
  | succ n ih =>
    intro i hn; unfold scanFor; split
    · rename_i h
      split
      · exact Or.inl rfl
      · rcases ih (i + 1) (by omega) with h' | h'
        · rw [h']; omega
        · exact Or.inr h'
    · exact Or.inl rfl

/-- No byte before the result is `c`. -/
theorem scanFor_ne (b : ByteArray) (c : UInt8) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → ∀ x ∈ (b.data.toList.drop i).take (scanFor b c stop i - i), x ≠ c := by
  intro n
  induction n with
  | zero => intro i hn x hx; unfold scanFor at hx; split at hx
            · omega
            · simp at hx
  | succ n ih =>
    intro i hn x hx; unfold scanFor at hx; split at hx
    · rename_i h
      split at hx
      · simp at hx
      · rename_i hc
        have hge := scanFor_ge b c stop _ (i + 1) rfl
        have hl : i < b.data.toList.length := by rw [Array.length_toList]; exact h.2
        rw [List.drop_eq_getElem_cons hl, show scanFor b c stop (i + 1) - i = (scanFor b c stop (i + 1) - (i + 1)) + 1 by omega,
          List.take_succ_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · subst hx; simpa [ByteArray.getElem_eq_getElem_data] using hc
        · exact ih (i + 1) (by omega) x hx
    · simp at hx

/-- The first index from `i`, before `stop`, whose byte satisfies `p`; or
where the search ran out. -/
@[specialize] def scanUntil (b : ByteArray) (p : UInt8 → Bool) (stop i : Nat) : Nat :=
  if h : i < stop ∧ i < b.size then (if p b[i] then i else scanUntil b p stop (i + 1)) else i
termination_by stop - i

theorem scanUntil_ge (b : ByteArray) (p : UInt8 → Bool) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → i ≤ scanUntil b p stop i := by
  intro n
  induction n with
  | zero => intro i hn; unfold scanUntil; split
            · omega
            · exact Nat.le_refl _
  | succ n ih =>
    intro i hn; unfold scanUntil; split
    · split
      · exact Nat.le_refl _
      · have := ih (i + 1) (by omega); omega
    · exact Nat.le_refl _

theorem scanUntil_le (b : ByteArray) (p : UInt8 → Bool) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → scanUntil b p stop i = i ∨ (scanUntil b p stop i ≤ stop ∧ scanUntil b p stop i ≤ b.size) := by
  intro n
  induction n with
  | zero => intro i hn; unfold scanUntil; split
            · omega
            · exact Or.inl rfl
  | succ n ih =>
    intro i hn; unfold scanUntil; split
    · split
      · exact Or.inl rfl
      · rcases ih (i + 1) (by omega) with h' | h'
        · rw [h']; omega
        · exact Or.inr h'
    · exact Or.inl rfl

/-- No byte before the result satisfies `p`. -/
theorem scanUntil_ne (b : ByteArray) (p : UInt8 → Bool) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → ∀ x ∈ (b.data.toList.drop i).take (scanUntil b p stop i - i), p x = false := by
  intro n
  induction n with
  | zero => intro i hn x hx; unfold scanUntil at hx; split at hx
            · omega
            · simp at hx
  | succ n ih =>
    intro i hn x hx; unfold scanUntil at hx; split at hx
    · rename_i h
      split at hx
      · simp at hx
      · rename_i hc
        have hge := scanUntil_ge b p stop _ (i + 1) rfl
        have hl : i < b.data.toList.length := by rw [Array.length_toList]; exact h.2
        rw [List.drop_eq_getElem_cons hl, show scanUntil b p stop (i + 1) - i = (scanUntil b p stop (i + 1) - (i + 1)) + 1 by omega,
          List.take_succ_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · subst hx; simpa [ByteArray.getElem_eq_getElem_data] using hc
        · exact ih (i + 1) (by omega) x hx
    · simp at hx

/-! ### Scanning with machine words

`scanUntil` counts with `Nat`; `scanUntilU` is the same loop on `USize`
indices, about twice as fast. `scanUntil_eq_fast` proves the switch sound
(`@[csimp]`), and `scanFor` runs as `scanUntil` with `(· == c)`. -/

theorem toNat_toUSize {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize]
  exact Nat.mod_eq_of_lt (by simpa [USize.size] using h)

/-- `scanUntil` on word indices, up to `stop ≤ b.size`. -/
@[specialize] def scanUntilU (b : ByteArray) (p : UInt8 → Bool) (stop : USize) (hs : stop.toNat ≤ b.size)
    (i : USize) : USize :=
  if h : i < stop then
    if p (b.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega)) then i else scanUntilU b p stop hs (i + 1)
  else i
termination_by stop.toNat - i.toNat
decreasing_by
  rw [USize.lt_iff_toNat_lt] at h
  have : (i + 1).toNat = i.toNat + 1 := by
    rw [USize.toNat_add]; simp only [USize.toNat_one]
    exact Nat.mod_eq_of_lt (by have := stop.toNat_lt_two_pow_numBits; omega)
  omega

theorem scanUntil_min (b : ByteArray) (p : UInt8 → Bool) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → scanUntil b p stop i = scanUntil b p (min stop b.size) i := by
  intro n
  induction n with
  | zero =>
    intro i hn; unfold scanUntil; split
    · omega
    · split
      · omega
      · rfl
  | succ n ih =>
    intro i hn
    rw [scanUntil.eq_1 b p stop i, scanUntil.eq_1 b p (min stop b.size) i]
    by_cases h : i < stop ∧ i < b.size
    · have h' : i < min stop b.size ∧ i < b.size := ⟨by omega, h.2⟩
      simp only [h, h', and_self, ↓reduceDIte]
      split
      · rfl
      · exact ih (i + 1) (by omega)
    · have h' : ¬ (i < min stop b.size ∧ i < b.size) := by omega
      simp only [h, h', ↓reduceDIte]

theorem scanUntilU_eq (b : ByteArray) (p : UInt8 → Bool) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i : USize), stop.toNat - i.toNat = n →
      (scanUntilU b p stop hs i).toNat = scanUntil b p stop.toNat i.toNat := by
  intro n
  induction n with
  | zero =>
    intro i hn
    unfold scanUntilU scanUntil
    have h1 : ¬ i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    have h2 : ¬ (i.toNat < stop.toNat ∧ i.toNat < b.size) := by omega
    simp only [h1, h2, ↓reduceDIte]
  | succ n ih =>
    intro i hn
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    have h2 : i.toNat < stop.toNat ∧ i.toNat < b.size := ⟨by omega, by omega⟩
    rw [scanUntilU.eq_1, scanUntil.eq_1]
    simp only [h1, h2, and_self, ↓reduceDIte]
    have hget : b.uget i (by omega) = b[i.toNat] := rfl
    rw [hget]
    split
    · rfl
    · have hi : (i + 1).toNat = i.toNat + 1 := by
        rw [USize.toNat_add]; simp only [USize.toNat_one]
        exact Nat.mod_eq_of_lt (by have := stop.toNat_lt_two_pow_numBits; omega)
      rw [ih (i + 1) (by omega), hi]

theorem usize_add_toNat (i : USize) (k : Nat) (h : i.toNat + k < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  have hk : (USize.ofNat k).toNat = k := by
    simp only [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)

/-- The block guard, on words: `i < stop` and `8 ≤ stop - i`. -/
theorem guard8 (i stop : USize) : i < stop ∧ USize.ofNat 8 ≤ stop - i ↔ i.toNat + 8 ≤ stop.toNat := by
  have h8 : (USize.ofNat 8).toNat = 8 := by
    simp only [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by cases System.Platform.numBits_eq <;> simp_all)
  constructor
  · rintro ⟨h1, h2⟩
    rw [USize.lt_iff_toNat_lt] at h1
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (USize.le_of_lt (USize.lt_iff_toNat_lt.mpr h1)), h8] at h2
    omega
  · intro h
    have h1 : i < stop := by rw [USize.lt_iff_toNat_lt]; omega
    refine ⟨h1, ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (USize.le_of_lt h1), h8]; omega

/-- `scanUntilU`, eight bytes at a time while none of them is a match:
fewer branches per byte for a predicate of several comparisons. -/
@[specialize] def scanUntilU8 (b : ByteArray) (p : UInt8 → Bool) (stop : USize) (hs : stop.toNat ≤ b.size)
    (i : USize) : USize :=
  if h' : i < stop ∧ USize.ofNat 8 ≤ stop - i then
    have h : i.toNat + 8 ≤ stop.toNat := (guard8 i stop).mp h'
    have hb : ∀ k, k < 8 → (i + USize.ofNat k).toNat < b.size := fun k hk => by
      rw [usize_add_toNat i k (by have := stop.toNat_lt_two_pow_numBits; simp [USize.size]; omega)]; omega
    -- `|||` of the flags, not `||`: no branch per byte
    if ((p (b.uget (i + USize.ofNat 0) (hb 0 (by decide)))).toUInt8 ||| (p (b.uget (i + USize.ofNat 1) (hb 1 (by decide)))).toUInt8 |||
        (p (b.uget (i + USize.ofNat 2) (hb 2 (by decide)))).toUInt8 ||| (p (b.uget (i + USize.ofNat 3) (hb 3 (by decide)))).toUInt8 |||
        (p (b.uget (i + USize.ofNat 4) (hb 4 (by decide)))).toUInt8 ||| (p (b.uget (i + USize.ofNat 5) (hb 5 (by decide)))).toUInt8 |||
        (p (b.uget (i + USize.ofNat 6) (hb 6 (by decide)))).toUInt8 ||| (p (b.uget (i + USize.ofNat 7) (hb 7 (by decide)))).toUInt8) != 0 then
      scanUntilU b p stop hs i
    else scanUntilU8 b p stop hs (i + USize.ofNat 8)
  else scanUntilU b p stop hs i
termination_by stop.toNat - i.toNat
decreasing_by
  have _h := (guard8 i stop).mp h'
  rw [usize_add_toNat i 8 (by have := stop.toNat_lt_two_pow_numBits; simp [USize.size]; omega)]; omega

/-- A byte that does not match is skipped. -/
theorem scanUntil_skip (b : ByteArray) (p : UInt8 → Bool) (stop i : Nat) (h : i < stop ∧ i < b.size)
    (hp : p b[i] = false) : scanUntil b p stop i = scanUntil b p stop (i + 1) := by
  rw [scanUntil.eq_1]; simp only [h, and_self, ↓reduceDIte, hp, Bool.false_eq_true, ↓reduceIte]

theorem scanUntil_skipN (b : ByteArray) (p : UInt8 → Bool) (stop i : Nat) :
    ∀ m, (∀ k, k < m → ∃ h : i + k < stop ∧ i + k < b.size, p (b[i + k]'h.2) = false) →
      scanUntil b p stop i = scanUntil b p stop (i + m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hall
    rw [ih (fun k hk => hall k (by omega))]
    obtain ⟨h, hp⟩ := hall m (by omega)
    rw [scanUntil_skip b p stop (i + m) h hp]; rfl

theorem scanUntilU8_eq (b : ByteArray) (p : UInt8 → Bool) (stop : USize) (hs : stop.toNat ≤ b.size) :
    ∀ (n : Nat) (i : USize), stop.toNat - i.toNat = n →
      (scanUntilU8 b p stop hs i).toNat = scanUntil b p stop.toNat i.toNat := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hn
    rw [scanUntilU8.eq_1]
    split
    · rename_i h'
      have h := (guard8 i stop).mp h'
      have hsz : i.toNat + 8 < USize.size := by
        have := stop.toNat_lt_two_pow_numBits; simp [USize.size]; omega
      have hadd : ∀ k, k ≤ 8 → (i + USize.ofNat k).toNat = i.toNat + k := fun k hk =>
        usize_add_toNat i k (by omega)
      dsimp only
      split
      · exact scanUntilU_eq b p stop hs _ i rfl
      · rename_i hp
        have tb : ∀ x : Bool, x.toUInt8 = 0 → x = false := by decide
        simp only [bne_iff_ne, ne_eq, Decidable.not_not, UInt8.or_eq_zero_iff] at hp
        obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hp
        replace h0 := tb _ h0; replace h1 := tb _ h1; replace h2 := tb _ h2; replace h3 := tb _ h3
        replace h4 := tb _ h4; replace h5 := tb _ h5; replace h6 := tb _ h6; replace h7 := tb _ h7
        have g : ∀ k (hk : k < 8), b.uget (i + USize.ofNat k) (by rw [hadd k (by omega)]; omega) = b[i.toNat + k]'(by omega) :=
          fun k hk => by
            have e := hadd k (by omega)
            simp only [ByteArray.uget, ByteArray.getElem_eq_getElem_data]
            show b.data[(i + USize.ofNat k).toNat]'_ = _
            simp only [e]
        rw [ih (stop.toNat - (i + USize.ofNat 8).toNat) (by rw [hadd 8 (by omega)]; omega) _ rfl, hadd 8 (by omega)]
        refine (scanUntil_skipN b p _ _ 8 (fun k hk => ⟨⟨by omega, by omega⟩, ?_⟩)).symm
        rw [← g k hk]
        match k, hk with
        | 0, _ => exact h0
        | 1, _ => exact h1
        | 2, _ => exact h2
        | 3, _ => exact h3
        | 4, _ => exact h4
        | 5, _ => exact h5
        | 6, _ => exact h6
        | 7, _ => exact h7
    · exact scanUntilU_eq b p stop hs _ i rfl

/-- `scanUntil`, on word indices when they fit. -/
@[inline] def scanUntilFast (b : ByteArray) (p : UInt8 → Bool) (stop i : Nat) : Nat :=
  let e := min stop b.size
  if h : e < USize.size ∧ i ≤ e then
    (scanUntilU8 b p e.toUSize (by rw [toNat_toUSize h.1]; omega) i.toUSize).toNat
  else scanUntil b p stop i

@[csimp] theorem scanUntil_eq_fast : @scanUntil = @scanUntilFast := by
  funext b p stop i
  unfold scanUntilFast
  dsimp only
  split
  · rename_i h
    rw [scanUntilU8_eq b p _ _ _ _ rfl, toNat_toUSize h.1, toNat_toUSize (by omega),
      ← scanUntil_min b p stop _ i rfl]
  · rfl

theorem scanFor_eq_scanUntil (b : ByteArray) (c : UInt8) (stop : Nat) :
    ∀ (n i : Nat), stop - i = n → scanFor b c stop i = scanUntil b (· == c) stop i := by
  intro n
  induction n with
  | zero => intro i hn; unfold scanFor scanUntil; split
            · omega
            · rfl
  | succ n ih =>
    intro i hn
    rw [scanFor.eq_1, scanUntil.eq_1]
    split
    · simp only [beq_iff_eq]
      split
      · rfl
      · exact ih (i + 1) (by omega)
    · rfl

/-- `scanFor`, as compiled. -/
@[inline] def scanForFast (b : ByteArray) (c : UInt8) (stop i : Nat) : Nat := scanUntilFast b (· == c) stop i

@[csimp] theorem scanFor_eq_fast : @scanFor = @scanForFast := by
  funext b c stop i
  rw [scanFor_eq_scanUntil b c stop _ i rfl, scanUntil_eq_fast]; rfl

/-- Copying `n` bytes of `a` from `i` onto the end of `b` (growing its
capacity geometrically) appends them. -/
theorem copySlice_end (a b : ByteArray) (i n : Nat) (exact : Bool) :
    a.copySlice i b b.size n exact = b ++ a.extract i (i + n) := by
  apply ByteArray.ext
  simp only [ByteArray.copySlice, ByteArray.data_append, ByteArray.data_extract]
  have h1 : b.data.extract 0 b.size = b.data := Array.extract_eq_self_of_le (Nat.le_refl _)
  have h2 : b.data.extract (b.size + min n (a.data.size - i)) = #[] := by
    apply Array.ext'; rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_of_length_le]
    · exact List.take_nil
    · rw [Array.length_toList]; exact Nat.le_add_right _ _
  rw [h1, h2, Array.append_empty]

/-- The bytes `[i, i + n)` of `b`, as a list, are those of `b.extract i (i + n)`. -/
theorem extract_toList (b : ByteArray) (i n : Nat) :
    (b.extract i (i + n)).data.toList = (b.data.toList.drop i).take n := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]

/-- A byte machine: a transition on one byte, a byte counter and an input
limit, and optionally a shortcut (`span`, `bulk`) for a run of bytes the
machine handles all alike, which `feedA` uses and the proofs never see. -/
structure Machine (σ : Type) where
  step : σ → UInt8 → σ
  pos : σ → Nat
  limit : Option Nat
  /-- How many of the bytes from index `i`, before `stop`, `bulk` can take at once (0: none). -/
  span : σ → ByteArray → Nat → Nat → Nat := fun _ _ _ _ => 0
  /-- Take `n` bytes from index `i` at once. -/
  bulk : σ → ByteArray → Nat → Nat → σ := fun s _ _ _ => s
  span_le : ∀ s b i stop, span s b i stop ≤ stop - i := by intros; exact Nat.zero_le _
  bulk_eq : ∀ s b i stop, bulk s b i (span s b i stop) =
    ((b.data.toList.drop i).take (span s b i stop)).foldl step s := by intros; rfl

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
def feedA (s : σ) (b : ByteArray) : σ :=
  bytesFoldRun M.step M.span M.bulk (fun _ => false) b (M.room s b.size) 0 s

theorem feedA_fold (s : σ) (b : ByteArray) : M.feedA s b = bytesFold M.step b (M.room s b.size) 0 s :=
  bytesFoldRun_eq _ _ _ _ (fun _ _ h => by cases h) M.span_le M.bulk_eq b _ _ 0 s rfl

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
  rw [feedA_fold]
  unfold feedT feed
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

/-- Feed a byte array, stopping when the machine halts. -/
def feedAUntil (halted : σ → Bool) (s : σ) (b : ByteArray) : σ :=
  bytesFoldRun M.step M.span M.bulk halted b (M.room s b.size) 0 s

theorem feedAUntil_eq {halted : σ → Bool} (hfix : ∀ s c, halted s = true → M.step s c = s)
    (s : σ) (b : ByteArray) : M.feedAUntil halted s b = M.feedA s b := by
  unfold feedAUntil
  rw [feedA_fold]
  exact bytesFoldRun_eq _ _ _ _ hfix M.span_le M.bulk_eq b _ _ 0 s rfl

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
