import LeanMultipart.RepoImpl.Form
import LeanMultipart.Proofs.MultipartStream

/-!
# The form layer: limit proofs

What Starlette's limits guarantee of an accepted form: at most `maxFields`
fields and `maxFiles` files, and every field within `maxPartSize`.
-/

namespace LeanMultipart
namespace Starlette

/-- An accepted urlencoded form respects `max_fields` and `max_part_size`. -/
theorem checkFields_ok (lim : FormLimits) (fs : List QsField) :
    ∀ (n : Nat) (r : List QsField), n ≤ lim.maxFields → checkFields lim n fs = .ok r →
      n + r.length ≤ lim.maxFields ∧ ∀ f ∈ r, f.1.size + f.2.size ≤ lim.maxPartSize := by
  induction fs with
  | nil => intro n r hn h; simp [checkFields] at h; subst h; simpa using hn
  | cons f fs ih =>
    intro n r hn h
    simp only [checkFields] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2
        cases hr : checkFields lim (n + 1) fs with
        | error e => rw [hr] at h; cases h
        | ok r' =>
          rw [hr] at h; simp [Except.map] at h; subst h
          have := ih (n + 1) r' (by omega) hr
          refine ⟨by simp; omega, ?_⟩
          intro g hg
          simp at hg
          rcases hg with rfl | hg
          · omega
          · exact this.2 g hg

theorem partOf_data {p : RawPart} {sp : StarlettePart} (h : partOf p = .ok sp) : sp.data = p.body := by
  unfold partOf at h
  simp only at h
  split at h
  · cases h; rfl
  · cases h

theorem checkPart_ok (lim : FormLimits) (nf nd : Nat) (p : RawPart) (sp : StarlettePart) (nf' nd' : Nat)
    (h : checkPart lim nf nd p = .ok (sp, nf', nd')) :
    (sp.isFile = true ∧ nf' = nf + 1 ∧ nf' ≤ lim.maxFiles ∧ nd' = nd) ∨
    (sp.isFile = false ∧ nf' = nf ∧ nd' = nd + 1 ∧ nd' ≤ lim.maxFields ∧ sp.data.size ≤ lim.maxPartSize) := by
  unfold checkPart at h
  cases hp : partOf p with
  | error e => rw [hp] at h; cases h
  | ok sp0 =>
    rw [hp] at h
    simp only [bind, Except.bind] at h
    have hd := partOf_data hp
    split at h
    · rename_i hf; split at h
      · cases h
      · cases h; left; exact ⟨hf, rfl, by omega, rfl⟩
    · rename_i hf; split at h
      · cases h
      · split at h
        · cases h
        · cases h; right
          exact ⟨by simpa using hf, rfl, rfl, by omega, by rw [hd]; omega⟩

/-- An accepted multipart form respects `max_files`, `max_fields` and
`max_part_size`. -/
theorem checkParts_ok (lim : FormLimits) (ps : List RawPart) :
    ∀ (nf nd : Nat) (sps : List StarlettePart) (nf' nd' : Nat),
      nf ≤ lim.maxFiles → nd ≤ lim.maxFields → checkParts lim nf nd ps = .ok (sps, nf', nd') →
      nf' = nf + (sps.filter (·.isFile)).length ∧ nd' = nd + (sps.filter (! ·.isFile)).length ∧
      nf' ≤ lim.maxFiles ∧ nd' ≤ lim.maxFields ∧
      ∀ sp ∈ sps, sp.isFile = false → sp.data.size ≤ lim.maxPartSize := by
  induction ps with
  | nil => intro nf nd sps nf' nd' h1 h2 h; simp [checkParts] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp_all
  | cons p ps ih =>
    intro nf nd sps nf' nd' h1 h2 h
    simp only [checkParts, bind, Except.bind] at h
    cases hc : checkPart lim nf nd p with
    | error e => rw [hc] at h; cases h
    | ok r =>
      obtain ⟨sp, a, b⟩ := r
      rw [hc] at h
      simp only at h
      cases hr : checkParts lim a b ps with
      | error e => rw [hr] at h; cases h
      | ok r' =>
        obtain ⟨sps', c, d⟩ := r'
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rcases checkPart_ok lim nf nd p sp a b hc with ⟨hf, ha, ha', hb⟩ | ⟨hf, ha, hb, hb', hs⟩
        · have := ih a b sps' c d ha' (by omega) hr
          refine ⟨?_, ?_, this.2.2.1, this.2.2.2.1, ?_⟩
          · simp [List.filter_cons, hf]; omega
          · simp [List.filter_cons, hf]; omega
          · intro x hx hxf; simp at hx; rcases hx with rfl | hx
            · simp_all
            · exact this.2.2.2.2 x hx hxf
        · have := ih a b sps' c d (by omega) hb' hr
          refine ⟨?_, ?_, this.2.2.1, this.2.2.2.1, ?_⟩
          · simp [List.filter_cons, hf]; omega
          · simp [List.filter_cons, hf]; omega
          · intro x hx hxf; simp at hx; rcases hx with rfl | hx
            · exact hs
            · exact this.2.2.2.2 x hx hxf

theorem ofMultipart_ok (lim : FormLimits) (r : MultipartResult) (sps : List StarlettePart)
    (h : ofMultipart lim r = .ok sps) :
    (sps.filter (·.isFile)).length ≤ lim.maxFiles ∧ (sps.filter (! ·.isFile)).length ≤ lim.maxFields ∧
      ∀ sp ∈ sps, sp.isFile = false → sp.data.size ≤ lim.maxPartSize := by
  unfold ofMultipart at h
  simp only [bind, Except.bind] at h
  cases hc : checkParts lim 0 0 r.parts with
  | error e => rw [hc] at h; cases h
  | ok x =>
    obtain ⟨sps', nf, nd⟩ := x
    rw [hc] at h
    have := checkParts_ok lim r.parts 0 0 sps' nf nd (Nat.zero_le _) (Nat.zero_le _) hc
    have hs : sps' = sps := by
      simp only at h
      split at h <;> (try split at h) <;> (try split at h) <;> simp_all [pure, Except.pure] <;>
        (try split at h) <;> simp_all
    subst hs
    exact ⟨by omega, by omega, this.2.2.2.2⟩

/-- An accepted urlencoded form is within the limits. -/
theorem parseUrlencodedRaw_ok (lim : FormLimits) (body : ByteArray) (fs : List QsField)
    (h : parseUrlencodedRaw lim body = .ok fs) :
    fs.length ≤ lim.maxFields ∧ ∀ f ∈ fs, f.1.size + f.2.size ≤ lim.maxPartSize := by
  unfold parseUrlencodedRaw at h
  split at h
  · have := checkFields_ok lim _ 0 fs (Nat.zero_le _) h
    exact ⟨by omega, this.2⟩
  · cases h

/-- An accepted multipart form is within the limits. -/
theorem parseMultipartRaw_ok (lim : FormLimits) (ct body : ByteArray) (ps : List StarlettePart)
    (h : parseMultipartRaw lim ct body = .ok ps) :
    (ps.filter (·.isFile)).length ≤ lim.maxFiles ∧ (ps.filter (! ·.isFile)).length ≤ lim.maxFields ∧
      ∀ sp ∈ ps, sp.isFile = false → sp.data.size ≤ lim.maxPartSize := by
  unfold parseMultipartRaw at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact ofMultipart_ok lim _ ps h

end Starlette

namespace FormParser

theorem bytes_append_toList (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem take_append_room (d a b : Bytes) (m : Nat) :
    a.take (min a.length (m - d.length)) ++
      b.take (min b.length (m - (d.length + (a.take (min a.length (m - d.length))).length))) =
    (a ++ b).take (min (a ++ b).length (m - d.length)) := by
  rw [Qs.take_min_length, List.length_take, Qs.take_min_length, Qs.take_min_length, List.take_append]
  by_cases h : a.length ≤ m - d.length
  · rw [List.take_of_length_le (l := a) h, Nat.min_eq_right h]
    congr 2; omega
  · rw [Nat.min_eq_left (by omega : m - d.length ≤ a.length),
      show m - (d.length + (m - d.length)) = 0 by omega, show m - d.length - a.length = 0 by omega]

/-- Writing two chunks is writing their concatenation. -/
theorem write_append (p : FormParser) (a b : ByteArray) : (p.write a).write b = p.write (a ++ b) := by
  cases p with
  | octet cfg fn data =>
    simp only [write]
    congr 1
    apply Array.ext'
    cases hm : cfg.maxBodySize with
    | none =>
      simp only [Array.toList_append, Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero,
        ByteArray.data_append, ByteArray.size, List.append_assoc, Array.size_append]
      rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp),
        List.take_of_length_le (by simp)]
    | some m =>
      simp only [Array.toList_append, Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero,
        ByteArray.data_append, Array.size_append, ByteArray.size, List.append_assoc, Array.length_toList]
      have := take_append_room data.toList a.data.toList b.data.toList m
      simp only [List.length_append, Array.length_toList, List.length_take] at this ⊢
      rw [← this, Array.size_extract, Nat.sub_zero]
  | qs cfg st => simp [write, bytes_append_toList, Qs.feedT_append]
  | mp cfg cx st => simp [write, bytes_append_toList, Mp.feedT_append]

theorem write_empty (p : FormParser) : p.write ByteArray.empty = p := by
  cases p with
  | octet cfg fn data =>
    simp only [write]; congr 1; apply Array.ext'; cases cfg.maxBodySize <;> simp [Array.toList_extract]
  | qs cfg st => simp [write, Qs.feedT, Qs.feed]
  | mp cfg cx st => simp [write, Mp.feedT, Mp.feed]

/-- Streaming equals whole-buffer for the form parser: any chunking of the
body gives the same fields and files. -/
theorem write_chunks (p : FormParser) (cs : List ByteArray) :
    cs.foldl write p = p.write (concat cs) := by
  induction cs generalizing p with
  | nil => exact (write_empty p).symm
  | cons c cs ih =>
    rw [List.foldl_cons, ih, write_append]
    congr 1

end FormParser

end LeanMultipart
