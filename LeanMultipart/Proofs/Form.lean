import LeanMultipart.RepoImpl.Form
import LeanMultipart.Proofs.MultipartStream
import LeanMultipart.Proofs.StepFacts
import LeanMultipart.Specifications.Multipart

/-!
# The form layer: limit proofs

What Starlette's limits guarantee of an accepted form: at most `maxFields`
fields and `maxFiles` files, and every field within `maxPartSize`.
-/

namespace LeanMultipart
namespace Starlette

theorem urlHalted_fix (lim : FormLimits) : ∀ s c, urlHalted s = true → (urlMachine lim).step s c = s := by
  intro s c h
  show urlStep lim s c = s
  unfold urlHalted at h
  unfold urlStep
  cases he : s.err with
  | some e => rfl
  | none => simp [he] at h

theorem mpHalted_fix (cx : Mp.Ctx) (lim : FormLimits) :
    ∀ s c, mpHalted s = true → (mpMachine cx lim).step s c = s := by
  intro s c h
  show mpStep cx lim s c = s
  unfold mpStep; simp [h]

/-! ## The urlencoded limits

`UrlInv`: while no limit error has been raised, every field read and the
field being read are within `max_part_size`, and there are at most
`max_fields` fields. The machine stops at the first byte that would break
this, so nothing beyond the limits is ever kept. -/

theorem urlInv_step (lim : FormLimits) (s : UrlState) (c : UInt8) (h : UrlInv lim s) :
    UrlInv lim (urlStep lim s c) := by
  unfold urlStep
  cases he : s.err with
  | some e => simp only; exact h
  | none =>
    obtain ⟨h1, h2, h3⟩ := h he
    simp only
    split
    · intro h'; simp at h'
    · split
      · intro h'; simp at h'
      · rename_i hs hn
        intro _
        show (Qs.step {} s.inner c).fields.size ≤ _ ∧ (∀ f ∈ (Qs.step {} s.inner c).fields.toList, _) ∧
          (Qs.step {} s.inner c).name.size + (Qs.step {} s.inner c).value.size ≤ _
        refine ⟨by omega, ?_, by omega⟩
        intro f hf
        rcases Qs.step_fields {} s.inner c with e | e
        · rw [e] at hf; exact h2 f hf
        · rw [e] at hf
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | rfl
          · exact h2 f hf
          · exact h3

theorem urlInv_feed (lim : FormLimits) (l : Bytes) : ∀ s, UrlInv lim s → UrlInv lim ((urlMachine lim).feed s l) := by
  induction l with
  | nil => intro s h; exact h
  | cons c cs ih => intro s h; exact ih _ (urlInv_step lim s c h)

theorem urlResult_ok (lim : FormLimits) (s : UrlState) (h : UrlInv lim s) (fs : List QsField)
    (hr : urlResult lim s = .ok fs) : Spec.UrlencodedWithinLimits lim fs := by
  unfold urlResult at hr
  cases he : s.err with
  | some e => rw [he] at hr; cases hr
  | none =>
    rw [he] at hr
    obtain ⟨h1, h2, h3⟩ := h he
    simp only at hr
    split at hr
    · cases hr
    · rename_i hn
      cases hr
      refine ⟨by simp; omega, ?_⟩
      intro f hf
      rcases Qs.finish_fields s.inner with e | e
      · rw [e] at hf; exact h2 f hf
      · rw [e] at hf
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | rfl
        · exact h2 f hf
        · exact h3

/-- An accepted urlencoded form is within the limits. -/
theorem parseUrlencodedRaw_ok (lim : FormLimits) (body : ByteArray) (fs : List QsField)
    (h : parseUrlencodedRaw lim body = .ok fs) : Spec.UrlencodedWithinLimits lim fs := by
  unfold parseUrlencodedRaw UrlencodedParser.write UrlencodedParser.finalize at h
  simp only at h
  rw [Machine.feedAUntil_eq _ (urlHalted_fix lim), Machine.feedA_eq] at h
  exact urlResult_ok lim _ (urlInv_feed lim _ {} (fun _ => ⟨by simp, by simp, by simp⟩)) fs h

/-- While no limit error is raised, the state is within the limits: the
machine stops at the byte that crosses one. -/
theorem urlencoded_bounded (lim : FormLimits) (body : ByteArray) :
    UrlInv lim (({ lim } : UrlencodedParser).write body).st := by
  unfold UrlencodedParser.write
  simp only
  rw [Machine.feedAUntil_eq _ (urlHalted_fix lim), Machine.feedA_eq]
  exact urlInv_feed lim _ {} (fun _ => ⟨by simp, by simp, by simp⟩)

/-! ## The multipart limits -/

theorem inData_iff (s : MState) : inData s = true ↔ Mp.InData s := by
  unfold inData Mp.InData; split <;> simp_all

theorem mpInv_step (cx : Mp.Ctx) (lim : FormLimits) (s : MpState) (c : UInt8) (h : MpInv lim s) :
    MpInv lim (mpStep cx lim s c) := by
  unfold mpStep
  split
  · exact h
  cases he : s.err with
  | some e => simp only; exact h
  | none =>
    obtain ⟨hf, hd, hbody, hcur, hcf, hcd⟩ := h he
    simp only
    have hsp := Mp.step_parts cx s.inner c
    generalize hi : Mp.step cx s.inner c = i' at hsp
    split
    · -- headers finished
      rename_i m hph hph'
      have hinA : inData s.inner = false := by simp [inData, hph]
      have hinB : inData i' = true := by simp [inData, hph']
      rcases hsp with ⟨hpar, hin⟩ | ⟨hin, hnin, _⟩
      · obtain ⟨hhd, hdat⟩ : i'.headers = s.inner.headers ∧ i'.data = ByteArray.empty := by
          rcases hin ((inData_iff i').1 hinB) with ⟨⟨m', hm'⟩, _⟩ | ⟨_, h1, h2⟩
          · simp [hph] at hm'
          · exact ⟨h1, h2⟩
        simp only [hinA, Bool.false_and, Bool.toNat_false, Nat.add_zero] at hcf hcd
        split
        · intro h'; simp at h'
        · rename_i hdp
          split
          · intro h'; simp at h'
          · rename_i hlt
            intro _
            simp only [hpar, hinB, Bool.true_and, Bool.toNat_true, Bool.not_true, Bool.toNat_false]
            refine ⟨by omega, hd, hbody, fun _ => ⟨by simp [hdp], fun h => by simp at h⟩, by omega, by simpa using hcd⟩
        · rename_i hdp
          split
          · intro h'; simp at h'
          · rename_i hlt
            intro _
            simp only [hpar, hinB, Bool.true_and, Bool.not_false, Bool.toNat_true, Bool.toNat_false]
            refine ⟨hf, by omega, hbody, fun _ => ⟨by simp [hdp], fun _ => by simp [hdat]⟩, by simpa using hcf, by omega⟩
      · exact absurd ((inData_iff _).2 hin) (by simp [hinA])
    · -- part data continues
      rename_i m m' hph hph'
      have hinA : inData s.inner = true := by simp [inData, hph]
      have hinB : inData i' = true := by simp [inData, hph']
      rcases hsp with ⟨hpar, hin⟩ | ⟨_, hnin, _⟩
      · have hhd : i'.headers = s.inner.headers := by
          rcases hin ((inData_iff i').1 hinB) with ⟨_, h1⟩ | ⟨h0, _, _⟩
          · exact h1
          · simp [hph] at h0
        obtain ⟨hcur1, hcur2⟩ := hcur hinA
        split
        · intro h'; simp at h'
        · rename_i hok
          intro _
          simp only [hpar, hinB, hinA] at hcf hcd ⊢
          refine ⟨hf, hd, hbody, fun _ => ⟨by rw [hhd]; exact hcur1, fun h => ?_⟩, hcf, hcd⟩
          simp [h] at hok; omega
      · exact absurd ((inData_iff _).1 hinB) hnin
    · -- every other step
      rename_i hne1 hne2
      intro _
      rcases hsp with ⟨hpar, hin⟩ | ⟨hin, hnin, hpush⟩
      · -- nothing completed; the new state is not in part data (else an earlier case)
        have hinB : inData i' = false := by
          cases hb : inData i'
          · rfl
          · rcases hin ((inData_iff i').1 hb) with ⟨⟨m, hm⟩, _⟩ | ⟨h0, _, _⟩
            · obtain ⟨m', hm'⟩ := (inData_iff i').1 hb
              exact (hne2 m m' hm hm').elim
            · obtain ⟨m', hm'⟩ := (inData_iff i').1 hb
              exact (hne1 m' h0 hm').elim
        simp only [hpar, hinB, Bool.false_and, Bool.toNat_false, Nat.add_zero]
        refine ⟨hf, hd, hbody, fun h => by simp at h, by omega, by omega⟩
      · -- a part completed
        have hinA : inData s.inner = true := (inData_iff _).2 hin
        have hinB : inData i' = false := by
          cases hb : inData i'
          · rfl
          · exact absurd ((inData_iff _).1 hb) hnin
        obtain ⟨hcur1, hcur2⟩ := hcur hinA
        simp only [hinA, hinB] at hcf hcd ⊢
        simp only [hpush, Array.toList_push, List.filter_append, List.length_append, Bool.false_and,
          Bool.toNat_false, Nat.add_zero]
        have hfile : isFileRaw ⟨s.inner.headers.toList, s.inner.data⟩ = s.curIsFile := by
          simp [isFileRaw, hcur1]
        refine ⟨hf, hd, ?_, fun h => by simp at h, ?_, ?_⟩
        · intro p hp hpf
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hbody p hp hpf
          · exact hcur2 (hfile ▸ hpf)
        · cases hc : s.curIsFile <;> simp_all
        · cases hc : s.curIsFile <;> simp_all

theorem mpInv_feed (cx : Mp.Ctx) (lim : FormLimits) (l : Bytes) :
    ∀ s, MpInv lim s → MpInv lim ((mpMachine cx lim).feed s l) := by
  induction l with
  | nil => intro s h; exact h
  | cons c cs ih => intro s h; exact ih _ (mpInv_step cx lim s c h)

theorem mpInv_init (lim : FormLimits) : MpInv lim {} := by
  intro _; simp [inData]

theorem partOf_ok {p : RawPart} {sp : StarlettePart} (h : partOf p = .ok sp) :
    sp.isFile = isFileRaw p ∧ sp.data = p.body := by
  unfold partOf at h
  simp only at h
  split at h
  · cases h; simp [StarlettePart.isFile, isFileRaw, *]
  · cases h

theorem mapM_partOf (ps : List RawPart) : ∀ sps, ps.mapM partOf = .ok sps →
    (sps.filter (·.isFile)).length = (ps.filter isFileRaw).length ∧
    (sps.filter (! ·.isFile)).length = (ps.filter (! isFileRaw ·)).length ∧
    ∀ sp ∈ sps, sp.isFile = false → ∃ p ∈ ps, isFileRaw p = false ∧ sp.data = p.body := by
  induction ps with
  | nil => intro sps h; simp [pure, Except.pure] at h; subst h; simp
  | cons p ps ih =>
    intro sps h
    rw [List.mapM_cons] at h
    cases hp : partOf p with
    | error e => rw [hp] at h; cases h
    | ok sp =>
      rw [hp] at h
      simp only [bind, Except.bind] at h
      cases hr : ps.mapM partOf with
      | error e => rw [hr] at h; cases h
      | ok sps' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := ih sps' hr
        obtain ⟨hf, hdat⟩ := partOf_ok hp
        refine ⟨?_, ?_, ?_⟩
        · cases hfr : isFileRaw p <;> simp_all 
        · cases hfr : isFileRaw p <;> simp_all 
        · intro x hx hxf
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨p, by simp, by rw [← hf]; exact hxf, hdat⟩
          · obtain ⟨q, hq, h⟩ := h3 x hx hxf
            exact ⟨q, by simp [hq], h⟩

theorem mpResult_ok (lim : FormLimits) (s : MpState) (h : MpInv lim s) (sps : List StarlettePart)
    (hr : mpResult s = .ok sps) : Spec.MultipartWithinLimits lim sps := by
  unfold mpResult at hr
  cases he : s.err with
  | some e => rw [he] at hr; cases hr
  | none =>
    rw [he] at hr
    obtain ⟨hf, hd, hbody, _, hcf, hcd⟩ := h he
    simp only at hr
    split at hr
    · cases hr
    · obtain ⟨h1, h2, h3⟩ := mapM_partOf _ sps hr
      refine ⟨by omega, by omega, ?_⟩
      intro sp hsp hspf
      obtain ⟨p, hp, hpf, hdat⟩ := h3 sp hsp hspf
      rw [hdat]; exact hbody p hp hpf

/-- An accepted multipart form is within the limits. -/
theorem parseMultipartRaw_ok (lim : FormLimits) (ct body : ByteArray) (ps : List StarlettePart)
    (h : parseMultipartRaw lim ct body = .ok ps) : Spec.MultipartWithinLimits lim ps := by
  unfold parseMultipartRaw at h
  split at h
  · cases h
  · split at h
    · cases h
    · unfold MultipartFormParser.write MultipartFormParser.finalize MultipartFormParser.new at h
      simp only at h
      rw [Machine.feedAUntil_eq _ (mpHalted_fix _ lim), Machine.feedA_eq] at h
      exact mpResult_ok lim _ (mpInv_feed _ lim _ {} (mpInv_init lim)) ps h

/-- While no limit error is raised, the multipart state is within the
limits: the machine stops at the byte that crosses one. -/
theorem multipart_bounded (b : Boundary) (lim : FormLimits) (body : ByteArray) :
    MpInv lim ((MultipartFormParser.new b lim).write body).st := by
  unfold MultipartFormParser.write MultipartFormParser.new
  simp only
  rw [Machine.feedAUntil_eq _ (mpHalted_fix _ lim), Machine.feedA_eq]
  exact mpInv_feed _ lim _ {} (mpInv_init lim)

/-- Starlette's urlencoded parser fed any chunking gives the result of one
write of the whole body. -/
theorem UrlencodedParser.finalize_chunks (p : UrlencodedParser) (cs : List ByteArray) :
    (cs.foldl UrlencodedParser.write p).finalize = (p.write (concatChunks cs)).finalize := by
  have hw : ∀ (q : UrlencodedParser) (c : ByteArray), q.write c = { q with st := (urlMachine q.lim).feedA q.st c } := by
    intro q c; unfold UrlencodedParser.write; rw [Machine.feedAUntil_eq _ (urlHalted_fix q.lim)]
  have : cs.foldl UrlencodedParser.write p = { p with st := cs.foldl (urlMachine p.lim).feedA p.st } := by
    induction cs generalizing p with
    | nil => rfl
    | cons c cs ih => simp only [List.foldl_cons]; rw [ih, hw]
  rw [this, (urlMachine p.lim).feedA_chunks (Or.inl rfl), hw]

/-- Starlette's multipart parser fed any chunking gives the result of one
write of the whole body. -/
theorem MultipartFormParser.finalize_chunks (p : MultipartFormParser) (cs : List ByteArray) :
    (cs.foldl MultipartFormParser.write p).finalize = (p.write (concatChunks cs)).finalize := by
  have hw : ∀ (q : MultipartFormParser) (c : ByteArray), q.write c = { q with st := (mpMachine q.cx q.lim).feedA q.st c } := by
    intro q c; unfold MultipartFormParser.write; rw [Machine.feedAUntil_eq _ (mpHalted_fix q.cx q.lim)]
  have : cs.foldl MultipartFormParser.write p = { p with st := cs.foldl (mpMachine p.cx p.lim).feedA p.st } := by
    induction cs generalizing p with
    | nil => rfl
    | cons c cs ih => simp only [List.foldl_cons]; rw [ih, hw]
  rw [this, (mpMachine p.cx p.lim).feedA_chunks (Or.inl rfl), hw]

end Starlette

namespace FormParser

theorem bytes_append_toList (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem take_append_room (d a b : Bytes) (m : Nat) :
    a.take (min a.length (m - d.length)) ++
      b.take (min b.length (m - (d.length + (a.take (min a.length (m - d.length))).length))) =
    (a ++ b).take (min (a ++ b).length (m - d.length)) := by
  rw [Machine.take_min_length, List.length_take, Machine.take_min_length, Machine.take_min_length, List.take_append]
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
        ByteArray.data_append, Array.size_append, ByteArray.size, List.append_assoc]
      have := take_append_room data.toList a.data.toList b.data.toList m
      simp only [List.length_append, Array.length_toList, List.length_take] at this ⊢
      rw [← this, Array.size_extract, Nat.sub_zero]
  | qs cfg st => simp [write, Qs.feedA_eq, Qs.feedT_append]
  | mp cfg cx st => simp [write, Mp.feedA_eq, Mp.feedT_append]

theorem write_empty (p : FormParser) : p.write ByteArray.empty = p := by
  cases p with
  | octet cfg fn data =>
    simp only [write]; congr 1; apply Array.ext'; cases cfg.maxBodySize <;> simp 
  | qs cfg st => simp [write, Qs.feedA_eq, Qs.feedT, Qs.feed]
  | mp cfg cx st => simp [write, Mp.feedA_eq, Mp.feedT, Mp.feed]

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
