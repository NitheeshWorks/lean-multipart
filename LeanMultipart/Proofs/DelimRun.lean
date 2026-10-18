import LeanMultipart.Proofs.MultipartRoundTrip
import LeanMultipart.RepoImpl.DelimRun

/-!
# Runs of part data up to the next delimiter: correctness

* `Mp.feed_run`: from a partial match of `k` bytes, bytes `x` such that
  `D.take k ++ x` holds no whole delimiter leave the machine at the partial
  match `pendL D (D.take k ++ x)`, with everything before it appended to the
  data. It strengthens `feed_body` by naming the match, which is what lets
  `runBulk` compute the state without stepping.
* `Mp.runBulk_eq`: the shortcut is the fold.
-/

namespace LeanMultipart
namespace Mp

/-! ## The suffix from the last `CR` -/

theorem crSuffix_append (a b : Bytes) :
    crSuffix (a ++ b) = match crSuffix b with
      | some s => some s
      | none => (crSuffix a).map (· ++ b) := by
  induction a with
  | nil => cases h : crSuffix b <;> simp [h, crSuffix]
  | cons c a ih =>
    simp only [List.cons_append, crSuffix, ih]
    cases hb : crSuffix b with
    | some s => rfl
    | none =>
      cases ha : crSuffix a with
      | some s => rfl
      | none => simp only [Option.map_none]; split <;> simp

theorem crSuffix_of_some {a b : Bytes} {s : Bytes} (h : crSuffix b = some s) : crSuffix (a ++ b) = some s := by
  rw [crSuffix_append, h]

theorem crSuffix_none_iff : ∀ l : Bytes, crSuffix l = none ↔ Byte.CR ∉ l
  | [] => by simp [crSuffix]
  | c :: l => by
    have ih := crSuffix_none_iff l
    simp only [crSuffix, List.mem_cons, not_or]
    cases h : crSuffix l with
    | some s =>
      have : Byte.CR ∈ l := Decidable.not_not.1 (fun h' => by rw [ih.2 h'] at h; cases h)
      simp [this]
    | none =>
      have := ih.1 h
      by_cases hc : c = Byte.CR
      · simp [hc]
      · simp [hc, this, Ne.symm hc]

/-- The suffix from the last `CR` starts with `CR` and is a suffix. -/
theorem crSuffix_some : ∀ {l s : Bytes}, crSuffix l = some s → (∃ t, s = Byte.CR :: t ∧ Byte.CR ∉ t) ∧ s <:+ l
  | [], s, h => by simp [crSuffix] at h
  | c :: l, s, h => by
    simp only [crSuffix] at h
    cases hl : crSuffix l with
    | some s' =>
      rw [hl] at h; cases h
      obtain ⟨h1, h2⟩ := crSuffix_some hl
      exact ⟨h1, h2.trans (List.suffix_cons _ _)⟩
    | none =>
      rw [hl] at h
      by_cases hc : c = Byte.CR
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h; subst h; subst hc
        exact ⟨⟨l, rfl, (crSuffix_none_iff l).1 hl⟩, List.suffix_refl _⟩
      · simp [hc] at h

variable (cx : Ctx)

/-- The delimiter is `CR` followed by bytes without `CR`. -/
theorem D_cons : ∃ T, D cx = Byte.CR :: T ∧ Byte.CR ∉ T := by
  refine ⟨[Byte.LF, Byte.HYPHEN, Byte.HYPHEN] ++ cx.boundary.toList, by simp [Boundary.delimL], ?_⟩
  have hb := cx.boundary.h_valid.2.2.1
  intro h
  rcases List.mem_append.1 h with h' | h'
  · revert h'; decide
  · exact absurd (hb _ h') (by decide)

theorem D_length : (D cx).length = cx.dlen := (dlen_eq cx).symm

/-- A prefix of the delimiter that starts at a `CR` of a prefix starts at its beginning. -/
theorem crSuffix_take (k : Nat) (hk1 : 1 ≤ k) : crSuffix ((D cx).take k) = some ((D cx).take k) := by
  obtain ⟨T, hT, hcr⟩ := D_cons cx
  rw [hT]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [List.take_succ_cons, crSuffix]
  have : crSuffix (T.take j) = none := (crSuffix_none_iff _).2 (fun h => hcr (List.mem_of_mem_take h))
  simp [this]

theorem pendL_take (k : Nat) (hk : k < cx.dlen) : pendL (D cx) ((D cx).take k) = k := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0; simp [pendL, crSuffix]
  · unfold pendL
    rw [crSuffix_take cx k h1]
    have hl : ((D cx).take k).length = k := by simp [D_length]; omega
    simp [hl, List.take_prefix, D_length, hk]

/-- `pendL` only looks at the last `dlen - 1` bytes. -/
theorem pendL_append_of_length (a x : Bytes) (hx : cx.dlen - 1 ≤ x.length) :
    pendL (D cx) (a ++ x) = pendL (D cx) x := by
  unfold pendL
  rw [crSuffix_append]
  cases hs : crSuffix x with
  | some s => rfl
  | none =>
    cases ha : crSuffix a with
    | none => rfl
    | some s =>
      obtain ⟨⟨t, rfl, _⟩, _⟩ := crSuffix_some ha
      simp only [Option.map_some]
      have : ¬ ((Byte.CR :: t ++ x).length < (D cx).length) := by simp [D_length]; omega
      rw [ite_eq_right (fun h => absurd h.1 this)]

theorem pendL_le (d l : Bytes) : pendL d l ≤ l.length := by
  unfold pendL
  split
  · exact Nat.zero_le _
  · rename_i s hs
    split
    · exact (crSuffix_some hs).2.length_le
    · exact Nat.zero_le _

theorem pendL_lt (l : Bytes) : pendL (D cx) l < cx.dlen := by
  have := dlen_ge cx
  unfold pendL
  split
  · omega
  · split
    · rename_i h; rw [D_length] at h; exact h.1
    · omega

/-! ## One step of a run -/

/-- With no whole delimiter ahead, the next byte keeps the machine in a
partial match, and the match it names is the one `pendL` reads. -/
theorem step_run (s : MState) (k : Nat) (hp : s.phase = .partData (.idx k)) (hk : k < cx.dlen)
    (c : UInt8) (rest : Bytes) (hinf : ¬ (D cx) <:+: ((D cx).take k ++ c :: rest)) :
    ∃ k1, ∃ pre : Bytes,
      step cx s c = { s with pos := s.pos + 1, phase := .partData (.idx k1), data := ⟨(s.data.data.toList ++ pre).toArray⟩ } ∧
      k1 < cx.dlen ∧
      pre ++ (D cx).take k1 = (D cx).take k ++ [c] ∧
      pendL (D cx) ((D cx).take k1 ++ rest) = pendL (D cx) ((D cx).take k ++ c :: rest) ∧
      ¬ (D cx) <:+: ((D cx).take k1 ++ rest) := by
  have h5 := dlen_ge cx
  have hkD : k < (D cx).length := by rw [D_length]; exact hk
  have hdata : ∀ (d : ByteArray), d = ⟨d.data.toList.toArray⟩ := fun d => by cases d; simp
  by_cases hc : c = cx.dAt k
  · have hcD : c = (D cx)[k] := by rw [hc, dAt_eq cx k hk]
    have htk : (D cx).take (k + 1) = (D cx).take k ++ [c] := by
      rw [hcD, List.take_succ_eq_append_getElem hkD]
    have hk1 : k + 1 ≠ cx.dlen := by
      intro he
      apply hinf
      have : (D cx).take k ++ [c] = D cx := by rw [← htk, List.take_of_length_le]; rw [D_length]; omega
      exact ⟨[], rest, by
        simp only [List.nil_append]
        rw [show D cx ++ rest = (D cx).take k ++ [c] ++ rest by rw [this]]; simp⟩
    refine ⟨k + 1, [], ?_, by omega, by simp [htk], by rw [htk]; simp, by rw [htk]; simpa using hinf⟩
    simp only [List.append_nil]; simp [step, hp, matchByte, ← hc, hk1]
  · have hinf' : ¬ (D cx) <:+: (c :: rest) := fun h => hinf (h.trans (List.suffix_append _ _).isInfix)
    by_cases hcr : c = Byte.CR
    · subst hcr
      have h1D : (D cx).take 1 = [Byte.CR] := by obtain ⟨T, hT, _⟩ := D_cons cx; rw [hT]; rfl
      refine ⟨1, (D cx).take k, ?_, by omega, by rw [h1D], ?_, by rw [h1D]; simpa using hinf'⟩
      · have e : s.data ++ cx.delim.extract 0 k = ⟨(s.data.data.toList ++ (D cx).take k).toArray⟩ := by
          apply ByteArray.ext_toList; simp [ByteArray.data_append, delim_toList]
        rw [← e]
        simp [step, hp, matchByte, hc, restart] <;> (try (intro h; subst h; simp [ByteArray.extract_same]))
      · rw [h1D]; unfold pendL
        have hs : ∃ u, crSuffix (Byte.CR :: rest) = some u := by
          simp only [crSuffix]; cases crSuffix rest <;> simp
        obtain ⟨u, hu⟩ := hs
        rw [show [Byte.CR] ++ rest = Byte.CR :: rest from rfl, crSuffix_of_some hu, hu]
    · refine ⟨0, (D cx).take k ++ [c], ?_, by omega, by simp, ?_, by simpa using fun h => hinf' (h.trans (List.suffix_cons _ _).isInfix)⟩
      · have e : (s.data ++ cx.delim.extract 0 k).push c = ⟨(s.data.data.toList ++ ((D cx).take k ++ [c])).toArray⟩ := by
          apply ByteArray.ext_toList; simp [ByteArray.data_append, delim_toList]
        rw [← e]
        simp [step, hp, matchByte, hc, restart, hcr] <;> (try (intro h; subst h; simp [ByteArray.extract_same]))
      · -- the partial match fails: neither side has a pending match unless `rest` does
        simp only [List.take_zero, List.nil_append]
        unfold pendL
        rw [show (D cx).take k ++ c :: rest = ((D cx).take k ++ [c]) ++ rest by simp, crSuffix_append]
        cases hr : crSuffix rest with
        | some s => rfl
        | none =>
          simp only
          cases ha : crSuffix ((D cx).take k ++ [c]) with
          | none => rfl
          | some u =>
            simp only [Option.map_some]
            have hpre : ¬ (u ++ rest <+: D cx) := by
              intro hpr
              obtain ⟨⟨t, rfl, ht⟩, hsuf⟩ := crSuffix_some ha
              -- `u` starts with `CR`, so it is the whole of `D.take k ++ [c]`
              have hk0 : k ≠ 0 := by
                intro h0; subst h0
                simp at hsuf
                rcases List.suffix_cons_iff.1 hsuf with h | h
                · simp at h; exact hcr h.1.symm
                · simp at h
              obtain ⟨T, hT, hcrT⟩ := D_cons cx
              have hu : Byte.CR :: t = (D cx).take k ++ [c] := by
                obtain ⟨w, hw⟩ := hsuf
                obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
                rw [hT, List.take_succ_cons, List.cons_append] at hw
                cases w with
                | nil => simpa [hT] using hw
                | cons w0 w =>
                  simp only [List.cons_append, List.cons.injEq] at hw
                  have : Byte.CR ∈ T.take j ++ [c] := by rw [← hw.2]; simp
                  rcases List.mem_append.1 this with h | h
                  · exact absurd (List.mem_of_mem_take h) hcrT
                  · simp at h; exact absurd h.symm hcr
              rw [hu] at hpr
              have hpr' : (D cx).take k ++ [c] <+: D cx := (List.prefix_append _ _).trans hpr
              have := List.prefix_iff_eq_take.1 hpr'
              have hlen : ((D cx).take k ++ [c]).length = k + 1 := by simp [D_length]; omega
              rw [hlen] at this
              apply hc
              rw [dAt_eq cx k hk]
              have h2 := congrArg (fun l => l[k]?) this
              have hlk : ((D cx).take k).length = k := by simp [D_length]; omega
              have h3 : ((D cx).take k ++ [c])[k]? = some c := by
                rw [List.getElem?_append_right (by omega), hlk]; simp
              simp only [h3, List.getElem?_take, show k < k + 1 by omega, ↓reduceIte,
                List.getElem?_eq_getElem hkD, Option.some.injEq] at h2
              exact h2
            simp [hpre]

/-- **A run.** From a partial match of `k` bytes, bytes `x` such that
`D.take k ++ x` holds no whole delimiter leave the machine at the partial
match `pendL D (D.take k ++ x)`; what precedes it is appended to the data. -/
theorem feed_run (x : Bytes) : ∀ (s : MState) (k : Nat), s.phase = .partData (.idx k) → k < cx.dlen →
    ¬ (D cx) <:+: ((D cx).take k ++ x) →
    ∃ pre : Bytes,
      feed cx s x = { s with pos := s.pos + x.length, phase := .partData (.idx (pendL (D cx) ((D cx).take k ++ x))), data := ⟨(s.data.data.toList ++ pre).toArray⟩ } ∧
      pre ++ (D cx).take (pendL (D cx) ((D cx).take k ++ x)) = (D cx).take k ++ x := by
  induction x with
  | nil =>
    intro s k hp hk _
    refine ⟨[], ?_, by simp [pendL_take cx k hk]⟩
    simp only [feed, List.foldl_nil, List.append_nil, pendL_take cx k hk, List.length_nil, Nat.add_zero, ← hp, ba_eta]
  | cons c rest ih =>
    intro s k hp hk hinf
    obtain ⟨k1, pre1, hs, hk1, hpre1, hpend, hinf1⟩ := step_run cx s k hp hk c rest hinf
    obtain ⟨pre2, hf, hpre2⟩ := ih (step cx s c) k1 (by rw [hs]) hk1 hinf1
    refine ⟨pre1 ++ pre2, ?_, ?_⟩
    · simp only [feed, List.foldl_cons] at hf ⊢
      rw [hf, ← hpend, hs]
      simp only [List.length_cons]
      congr 1
      · omega
      · apply ByteArray.ext_toList; simp
    · rw [← hpend, List.append_assoc, hpre2, ← List.append_assoc, hpre1]; simp

/-! ## Comparing and searching in place -/

theorem eqRun_iff (b : ByteArray) (i : Nat) (d : ByteArray) (j : Nat) :
    ∀ (m t : Nat), d.size - (j + t) = m →
      (eqRun b i d j t = true ↔ (d.data.toList.drop (j + t)) <+: (b.data.toList.drop (i + t))) := by
  intro m
  induction m with
  | zero =>
    intro t hm
    unfold eqRun
    rw [dite_eq_right (fun h => absurd h (by omega)), List.drop_of_length_le (l := d.data.toList) (by simp; omega)]
    simp
  | succ m ih =>
    intro t hm
    unfold eqRun
    rw [dite_eq_left (show j + t < d.size by omega)]
    have hdl : j + t < d.data.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hdl]
    by_cases hb : i + t < b.size
    · rw [dite_eq_left hb]
      have hbl : i + t < b.data.toList.length := by simp; omega
      rw [List.drop_eq_getElem_cons hbl, List.cons_prefix_cons, Bool.and_eq_true, beq_iff_eq,
        ih (t + 1) (by omega), show j + (t + 1) = j + t + 1 by omega, show i + (t + 1) = i + t + 1 by omega]
      simp [ByteArray.getElem_eq_getElem_data, eq_comm]
    · rw [dite_eq_right (fun h => absurd h hb), List.drop_of_length_le (l := b.data.toList) (by simp; omega)]
      simp

theorem eqRun_iff0 (b : ByteArray) (i : Nat) (d : ByteArray) (j : Nat) :
    eqRun b i d j 0 = true ↔ (d.data.toList.drop j) <+: (b.data.toList.drop i) :=
  eqRun_iff b i d j _ 0 rfl

theorem scanFor_ne_idx (b : ByteArray) (c : UInt8) (stop q j : Nat) (h1 : q ≤ j)
    (h2 : j < scanFor b c stop q) (h3 : j < b.size) : b[j] ≠ c := by
  have hne := scanFor_ne b c stop _ q rfl
  apply hne
  have hl : j < b.data.toList.length := by simp; omega
  have : b.data.toList[j] ∈ (b.data.toList.drop q).take (scanFor b c stop q - q) := by
    rw [List.mem_iff_getElem]
    refine ⟨j - q, by simp; omega, ?_⟩
    simp [show q + (j - q) = j by omega]
  simpa [ByteArray.getElem_eq_getElem_data] using this

/-- A prefix of `b.drop p` ends inside `b`, with `b`'s byte there. -/
theorem prefix_drop_last {d : Bytes} {b : ByteArray} {p : Nat} (hd : 0 < d.length)
    (h : d <+: b.data.toList.drop p) :
    ∃ hlt : p + d.length - 1 < b.size, b[p + d.length - 1] = d[d.length - 1]'(by omega) := by
  have hle : d.length ≤ b.size - p := by
    have := h.length_le; rw [List.length_drop] at this
    have h2 : b.data.toList.length = b.size := by simp
    omega
  refine ⟨by omega, ?_⟩
  obtain ⟨u, hu⟩ := h
  have := congrArg (fun l => l[d.length - 1]?) hu
  simp only [List.getElem?_append_left (show d.length - 1 < d.length by omega), List.getElem?_drop] at this
  have h2 : p + d.length - 1 < b.data.toList.length := by
    have : b.data.toList.length = b.size := by simp
    omega
  rw [show p + (d.length - 1) = p + d.length - 1 by omega, List.getElem?_eq_getElem h2,
    List.getElem?_eq_getElem (show d.length - 1 < d.length by omega)] at this
  simpa [ByteArray.getElem_eq_getElem_data] using this.symm

theorem findDelim_le (b d : ByteArray) (stop : Nat) : ∀ (m q : Nat), stop - q = m → findDelim b d stop q ≤ stop := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro q hm
    unfold findDelim
    simp only
    split
    · split
      · omega
      · have := scanFor_ge b (d[d.size - 1]?.getD 0) stop _ q rfl
        exact ih _ (by omega) _ rfl
    · exact Nat.le_refl _

/-- No delimiter starts before the result (with its last byte at `q` or later). -/
theorem findDelim_free (b d : ByteArray) (stop : Nat) (hd : 0 < d.size) :
    ∀ (m q : Nat), stop - q = m → ∀ p, q ≤ p + d.size - 1 → p + d.size ≤ findDelim b d stop q →
      ¬ d.data.toList <+: b.data.toList.drop p := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro q hm p hq hp hpre
    have hdl : 0 < d.data.toList.length := by simp; omega
    obtain ⟨hlt, heq⟩ := prefix_drop_last hdl hpre
    simp only [Array.length_toList, ByteArray.size_data] at hlt heq
    have hlast : d[d.size - 1]?.getD 0 = d[d.size - 1] := by
      rw [getElem?_pos d (d.size - 1) (by omega)]; rfl
    have heq' : b[p + d.size - 1] = d[d.size - 1] := by
      simpa [ByteArray.getElem_eq_getElem_data] using heq
    have hge := scanFor_ge b (d[d.size - 1]?.getD 0) stop _ q rfl
    generalize hq' : scanFor b (d[d.size - 1]?.getD 0) stop q = q' at hge
    -- the last byte of the occurrence is at or after the next candidate
    have hafter : q' ≤ p + d.size - 1 := by
      refine Nat.le_of_not_lt (fun hc => ?_)
      exact scanFor_ne_idx b (d[d.size - 1]?.getD 0) stop q (p + d.size - 1) hq (by rw [hq']; omega) hlt
        (by rw [hlast]; exact heq')
    unfold findDelim at hp
    simp only [hq'] at hp
    split at hp
    · rename_i hin
      split at hp
      · omega
      · rename_i hno
        by_cases he : p + d.size - 1 = q'
        · apply hno
          rw [eqRun_iff0]
          rw [show q' + 1 - d.size = p by omega]
          simpa using hpre
        · exact ih _ (by omega) (q' + 1) rfl p (by omega) hp hpre
    · rename_i hout
      -- no candidate left before `stop`: the occurrence would end past it
      have hle := scanFor_le b (d[d.size - 1]?.getD 0) stop _ q rfl
      rw [hq'] at hle
      rcases hle with h | h <;> omega

/-! ## The shortcut is the fold -/

theorem delim_size : cx.delim.size = cx.dlen := rfl

theorem drop_append_ge {l₁ l₂ : Bytes} {n : Nat} (h : l₁.length ≤ n) : (l₁ ++ l₂).drop n = l₂.drop (n - l₁.length) := by
  rw [List.drop_append, List.drop_of_length_le h, List.nil_append]

/-- What `runSpan` finds: a run at least as long as the delimiter, inside
the input and before `stop`, after which (with the pending match before
it) there is no whole delimiter. -/
theorem runSpan_spec (s : MState) (b : ByteArray) (i stop k : Nat) (hp : s.phase = .partData (.idx k))
    (hk : k < cx.dlen) (hn : runSpan cx s b i stop ≠ 0) :
    cx.dlen ≤ runSpan cx s b i stop ∧ i + runSpan cx s b i stop ≤ b.size ∧ i + runSpan cx s b i stop ≤ stop ∧
      ¬ (D cx) <:+: ((D cx).take k ++ (b.data.toList.drop i).take (runSpan cx s b i stop)) := by
  have h5 := dlen_ge cx
  revert hn
  unfold runSpan
  rw [hp]
  simp only
  rw [if_neg (show ¬ cx.dlen ≤ k by omega)]
  generalize hr : findDelim b cx.delim (min stop b.size) (i + cx.dlen - 1) = r
  intro hn
  have hr1 : ¬ r < i + cx.dlen := fun h => hn (if_pos h)
  rw [if_neg hr1] at hn ⊢
  have hr2 : ¬ (k != 0 && eqRun b i cx.delim k 0) = true := fun h => hn (if_pos h)
  rw [if_neg hr2]
  have hle : r ≤ min stop b.size := hr ▸ findDelim_le b cx.delim _ _ _ rfl
  refine ⟨by omega, by omega, by omega, ?_⟩
  rintro ⟨u, t, hut⟩
  have hDl : (D cx).length = cx.dlen := D_length cx
  have hxl : ((b.data.toList.drop i).take (r - i)).length = r - i := by simp; omega
  by_cases hu : k ≤ u.length
  · -- an occurrence inside the run
    have hdrop := congrArg (List.drop u.length) hut
    rw [List.append_assoc, List.drop_left, drop_append_ge (by simp; omega), List.length_take, hDl,
      Nat.min_eq_left (by omega)] at hdrop
    have hpre : D cx <+: ((b.data.toList.drop i).take (r - i)).drop (u.length - k) := hdrop ▸ List.prefix_append _ _
    have hlen := hpre.length_le
    rw [List.length_drop, hxl, hDl] at hlen
    rw [List.drop_take, List.drop_drop] at hpre
    have hpre' := hpre.trans (List.take_prefix _ _)
    rw [← delim_toList] at hpre'
    exact findDelim_free b cx.delim (min stop b.size) (by rw [delim_size]; omega) _ (i + cx.dlen - 1) rfl
      (i + (u.length - k)) (by rw [delim_size]; omega) (by rw [hr, delim_size]; omega) hpre'
  · -- an occurrence starting in the pending match starts at its `CR`
    have hk0 : k ≠ 0 := by omega
    have hu0 : u = [] := by
      have hget := congrArg (fun l => l[u.length]?) hut
      simp only [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hget
      have hr : ((D cx).take k ++ (b.data.toList.drop i).take (r - i))[u.length]? = (D cx)[u.length]? := by
        rw [List.getElem?_append_left (by simp; omega)]; simp [List.getElem?_take, show u.length < k by omega]
      rw [hr] at hget
      obtain ⟨T, hT, _⟩ := D_cons cx
      have hcr : (D cx)[u.length]? = some Byte.CR := by rw [← hget, hT]; simp
      cases hul : u.length with
      | zero => exact List.eq_nil_of_length_eq_zero hul
      | succ j =>
        exfalso
        have hj : j + 1 < cx.dlen := by omega
        apply dAt_ne_CR cx (j + 1) (by omega) hj
        rw [dAt_eq cx (j + 1) hj]
        rw [hul, List.getElem?_eq_getElem (by omega)] at hcr
        simpa using hcr
    subst hu0
    rw [List.nil_append] at hut
    have hrest : (D cx).drop k ++ t = (b.data.toList.drop i).take (r - i) := by
      have hut' : (D cx).take k ++ ((D cx).drop k ++ t) = (D cx).take k ++ (b.data.toList.drop i).take (r - i) := by
        rw [← List.append_assoc, List.take_append_drop]; exact hut
      exact List.append_cancel_left hut'
    have hpre : (D cx).drop k <+: b.data.toList.drop i :=
      (hrest ▸ List.prefix_append _ _).trans (List.take_prefix _ _)
    apply hr2
    rw [← delim_toList] at hpre
    simp [hk0, (eqRun_iff0 b i cx.delim k).2 hpre]

/-- The pending match and the part data together, as runBulk lays them out. -/
theorem copy_run (s : MState) (b : ByteArray) (i k m : Nat) :
    let d0 := if k = 0 then s.data else s.data ++ cx.delim.extract 0 k
    (b.copySlice i d0 d0.size m (d0.size == 0)).data.toList =
      s.data.data.toList ++ (D cx).take k ++ (b.data.toList.drop i).take m := by
  simp only
  rw [copySlice_end]
  split
  · rename_i h; subst h; simp [ByteArray.data_append, extract_toList]
  · simp [ByteArray.data_append, extract_toList, delim_toList]

/-- **The run shortcut is the fold.** -/
theorem runBulk_eq (s : MState) (b : ByteArray) (i stop : Nat) :
    runBulk cx s b i (runSpan cx s b i stop) = ((b.data.toList.drop i).take (runSpan cx s b i stop)).foldl (step cx) s := by
  by_cases h0 : runSpan cx s b i stop = 0
  · rw [h0]; unfold runBulk; split <;> simp
  · cases hp : s.phase with
    | partData m =>
      cases m with
      | idx k =>
        have hkd : k < cx.dlen := by
          refine Nat.lt_of_not_le (fun h => h0 ?_)
          simp [runSpan, hp, h]
        obtain ⟨hn1, hn2, _, hinf⟩ := runSpan_spec cx s b i stop k hp hkd h0
        generalize hn : runSpan cx s b i stop = n at hn1 hn2 hinf h0
        have h5 := dlen_ge cx
        obtain ⟨pre, hf, hpre⟩ := feed_run cx _ s k hp hkd hinf
        have hx : ((b.data.toList.drop i).take n).length = n := by simp; omega
        have hpend : pendL (D cx) ((b.extract (i + n - (cx.dlen - 1)) (i + n)).data.toList) =
            pendL (D cx) ((D cx).take k ++ (b.data.toList.drop i).take n) := by
          rw [pendL_append_of_length cx _ _ (by omega)]
          conv => rhs; rw [← List.take_append_drop (n - (cx.dlen - 1)) ((b.data.toList.drop i).take n)]
          rw [pendL_append_of_length cx _ _ (by simp; omega)]
          congr 1
          have he : b.extract (i + n - (cx.dlen - 1)) (i + n) =
              b.extract (i + n - (cx.dlen - 1)) ((i + n - (cx.dlen - 1)) + (cx.dlen - 1)) := by
            congr 1; omega
          rw [he, extract_toList, List.drop_take, List.drop_drop, show i + (n - (cx.dlen - 1)) = i + n - (cx.dlen - 1) by omega,
            show n - (n - (cx.dlen - 1)) = cx.dlen - 1 by omega]
        have hk'd := pendL_lt cx ((D cx).take k ++ (b.data.toList.drop i).take n)
        generalize hk' : pendL (D cx) ((D cx).take k ++ (b.data.toList.drop i).take n) = k' at hpend hpre hf hk'd
        have hk'n : k' < n := by omega
        unfold runBulk
        rw [hp]
        simp only [h0, ↓reduceIte, ← delim_toList, hpend]
        rw [delim_toList, hpend]
        show _ = feed cx s _
        rw [hf]
        congr 1
        · rw [hx]
        · apply ByteArray.ext_toList
          rw [copy_run]
          simp only [List.append_assoc]
          congr 1
          -- `pre` is the pending match and the run but for its last `k'` bytes
          have hsp : (D cx).take k ++ (b.data.toList.drop i).take n =
              ((D cx).take k ++ ((b.data.toList.drop i).take n).take (n - k')) ++ ((b.data.toList.drop i).take n).drop (n - k') := by
            simp
          have hlen := congrArg List.length hpre
          rw [hsp] at hpre
          simp only [List.length_append, List.length_take, hx, D_length, Nat.min_eq_left (Nat.le_of_lt hkd),
            Nat.min_eq_left (Nat.le_of_lt hk'd)] at hlen
          have := (List.append_inj hpre (by
            simp only [List.length_append, List.length_take, List.length_drop, hx, D_length, Nat.min_eq_left (Nat.le_of_lt hkd)]
            omega)).1
          rw [this, List.take_take, Nat.min_eq_left (by omega)]
      | _ => simp [runSpan, hp] at h0
    | _ => simp [runSpan, hp] at h0

end Mp
end LeanMultipart
