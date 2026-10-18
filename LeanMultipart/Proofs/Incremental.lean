import LeanMultipart.RepoImpl.Incremental
import LeanMultipart.Proofs.Stream
import LeanMultipart.Proofs.Form
import LeanMultipart.Proofs.DelimRun

/-!
# Starlette's incremental multipart parser: correctness

* `Starlette.MultipartStream.parseChunks_eq`: for every split of the body
  into chunks, the parts assembled from the events are those of the
  whole-buffer parse `Starlette.parseMultipartRaw`, or its error.
* `Starlette.MultipartStream.feed_retains`: between chunks the parser keeps
  no part data and no completed part, only the current part's headers.

The proof is an invariant between the whole-buffer state `W` (Starlette's
byte machine `mpStep`), the streaming state `P` and the parts assembled so
far. It reuses python-multipart's streaming invariant
(`MultipartParser.Inv`, with a collector of python-multipart's events as a
witness) and adds Starlette's counters, which agree because each check reads
the same phase, headers and data size on both sides.
-/

namespace LeanMultipart
namespace MultipartParser

/-- In part data, a step that stays in part data reports nothing. -/
theorem stepEv_data_data (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) {m m' : DelimMatch}
    (h : s.phase = .partData m) (h' : (Mp.step cx s c).phase = .partData m') :
    stepEv cx (s, evs) c = (Mp.step cx s c, evs) := by
  simp only [stepEv, h, h']

/-- The end of the headers reports `headersFinished`. -/
theorem stepEv_headers_done (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) {m' : DelimMatch}
    (h : s.phase = .headersAlmostDone) (h' : (Mp.step cx s c).phase = .partData m') :
    stepEv cx (s, evs) c = (Mp.step cx s c, evs.push .headersFinished) := by
  simp only [stepEv, h, h']

/-- Leaving part data, the step ends the part (at a boundary or at the end)
and completes it with the data read so far. -/
theorem step_leave (cx : Mp.Ctx) (s : MState) (c : UInt8) {m : DelimMatch} (h : s.phase = .partData m)
    (h' : ¬ Mp.InData (Mp.step cx s c)) :
    ((Mp.step cx s c).phase = .headerFieldStart ∨ (Mp.step cx s c).phase = .done) ∧
      (Mp.step cx s c).parts = s.parts.push ⟨s.headers.toList, s.data⟩ := by
  unfold Mp.InData at h'
  revert h'
  unfold Mp.step
  rw [h]
  cases m <;> simp only [Mp.matchByte, Mp.restart, Mp.beginPart, Mp.finishPart] <;> (repeat' split) <;> simp

/-- Leaving part data: the part's last data, `partEnd`, and `partBegin` or `end`. -/
theorem stepEv_leave (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) {m : DelimMatch}
    (h : s.phase = .partData m) (h' : ¬ Mp.InData (Mp.step cx s c)) :
    stepEv cx (s, evs) c = ({ Mp.step cx s c with parts := #[] },
      ((emitIf evs s.data .partData).push .partEnd).push
        (if (Mp.step cx s c).phase = .done then .end else .partBegin)) := by
  obtain ⟨hph, hparts⟩ := step_leave cx s c h h'
  have hlb : lastBody (Mp.step cx s c) = s.data := by simp [lastBody, hparts]
  rcases hph with hph | hph
  · simp only [stepEv, h, hph, hlb]; simp
  · simp only [stepEv, h, hph, hlb]; simp

/-- Outside part data, a step reports no part data and ends no part. -/
theorem stepEv_quiet (cx : Mp.Ctx) (s : MState) (c : UInt8) (h : ¬ Mp.InData s) :
    ∀ e ∈ (stepEv cx (s, #[]) c).2, (∀ b, e ≠ .partData b) ∧ e ≠ .partEnd := by
  unfold Mp.InData at h
  simp only [stepEv]
  split <;> simp_all [emitIf] <;> (try split) <;> (try simp_all)
  all_goals (intro e he; rcases he with ⟨_, rfl⟩ | rfl <;> simp)

end MultipartParser

namespace Starlette

open MultipartParser in
theorem halted_iff (s : PState) : s.halted = false ↔ s.err = none ∧ (∀ e, s.mp.phase ≠ .failed e) ∧ s.mp.phase ≠ .done := by
  unfold PState.halted
  cases s.err <;> simp <;> split <;> simp_all

theorem pStep_halted (cx : Mp.Ctx) (lim : FormLimits) (r : PState × Array PartEvent) (c : UInt8)
    (h : r.1.halted = true) : pStep cx lim r c = r := by
  obtain ⟨s, out⟩ := r
  simp only at h
  simp [pStep, h]

/-- A step appends its events to those already there. -/
theorem pStep_append (cx : Mp.Ctx) (lim : FormLimits) (s : PState) (out : Array PartEvent) (c : UInt8) :
    pStep cx lim (s, out) c = ((pStep cx lim (s, #[]) c).1, out ++ (pStep cx lim (s, #[]) c).2) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only [pStep]
  split
  · simp
  · generalize MultipartParser.stepEv cx (mp, #[]) c = E
    obtain ⟨m', evs⟩ := E
    simp only
    split
    all_goals (try split) <;> (try split) <;> (by_cases hev : evs = #[] <;> simp [hev, Array.append_assoc])

/-- A step of part data that stays in part data, within `max_part_size`
for a field, is python-multipart's step and reports nothing. -/
theorem pStep_run (cx : Mp.Ctx) (lim : FormLimits) (s : PState) (out : Array PartEvent) (c : UInt8)
    {m m' : DelimMatch} (he : s.err = none) (hp : s.mp.phase = .partData m)
    (hp' : (Mp.step cx s.mp c).phase = .partData m')
    (hsz : s.curIsFile = false → s.sent + (Mp.step cx s.mp c).data.size ≤ lim.maxPartSize) :
    pStep cx lim (s, out) c = ({ s with mp := Mp.step cx s.mp c }, out) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only at he hp hp' hsz
  subst he
  have hh : ({ mp, nFiles, nFields, curIsFile, sent, err := none } : PState).halted = false := by
    simp [PState.halted, hp]
  simp only [pStep, hh, Bool.false_eq_true, ↓reduceIte, MultipartParser.stepEv_data_data cx mp #[] c hp hp',
    Array.isEmpty_empty, hp, hp']
  cases curIsFile
  · have := hsz rfl; simp; omega
  · simp

/-- Lifting a run: if every step of `x` is a step of part data that stays
in part data within the limit, folding `pStep` is folding python-multipart's
step. -/
theorem foldl_pStep_run (cx : Mp.Ctx) (lim : FormLimits) (x : Bytes) : ∀ (s : PState) (out : Array PartEvent),
    s.err = none →
    (∀ y c, y ++ [c] <+: x → Mp.InData (Mp.feed cx s.mp y) ∧ Mp.InData (Mp.feed cx s.mp (y ++ [c])) ∧
      (s.curIsFile = false → s.sent + (Mp.feed cx s.mp (y ++ [c])).data.size ≤ lim.maxPartSize)) →
    x.foldl (pStep cx lim) (s, out) = ({ s with mp := Mp.feed cx s.mp x }, out) := by
  induction x with
  | nil => intro s out _ _; simp [Mp.feed]
  | cons c rest ih =>
    intro s out he h
    obtain ⟨⟨m, hm⟩, ⟨m', hm'⟩, hsz⟩ := h [] c (by simp)
    simp only [Mp.feed, List.foldl_nil, List.nil_append, List.foldl_cons, List.foldl_nil] at hm hm' hsz
    rw [List.foldl_cons, pStep_run cx lim s out c he hm hm' hsz]
    rw [ih { s with mp := Mp.step cx s.mp c } out he]
    · simp [Mp.feed]
    · intro y c' hy
      have := h (c :: y) c' (by simpa using List.prefix_cons_inj c |>.2 hy)
      simpa [Mp.feed] using this

theorem dataSize_feed_run (cx : Mp.Ctx) (s : MState) (k : Nat) (hp : s.phase = .partData (.idx k)) (hk : k < cx.dlen)
    (x : Bytes) (hinf : ¬ (Mp.D cx) <:+: ((Mp.D cx).take k ++ x)) :
    Mp.InData (Mp.feed cx s x) ∧ (Mp.feed cx s x).data.size ≤ s.data.size + k + x.length := by
  obtain ⟨pre, hf, hpre⟩ := Mp.feed_run cx x s k hp hk hinf
  rw [hf]
  refine ⟨⟨_, rfl⟩, ?_⟩
  have := congrArg List.length hpre
  simp only [List.length_append, List.length_take, Mp.D_length] at this
  show (⟨(s.data.data.toList ++ pre).toArray⟩ : ByteArray).size ≤ s.data.size + k + x.length
  rw [show (⟨(s.data.data.toList ++ pre).toArray⟩ : ByteArray).size = s.data.size + pre.length by
    simp only [ByteArray.size, List.size_toArray, List.length_append, Array.length_toList]]
  have : min k cx.dlen ≤ k := Nat.min_le_left _ _
  omega

/-- The run shortcut of the stream is the fold. -/
theorem pBulk_eq (cx : Mp.Ctx) (lim : FormLimits) (r : PState × Array PartEvent) (b : ByteArray) (i stop : Nat) :
    pBulk cx r b i (pSpan cx lim r b i stop) = ((b.data.toList.drop i).take (pSpan cx lim r b i stop)).foldl (pStep cx lim) r := by
  obtain ⟨⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out⟩ := r
  by_cases h0 : pSpan cx lim (⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out) b i stop = 0
  · rw [h0]; simp only [pBulk, List.take_zero, List.foldl_nil]
    unfold Mp.runBulk; split <;> simp
  · have he : err = none := by
      cases err
      · rfl
      · simp [pSpan] at h0
    subst he
    simp only [pSpan, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
    generalize hst : pStop cx lim ⟨mp, nFiles, nFields, curIsFile, sent, none⟩ i stop = stop' at h0 ⊢
    cases hp : mp.phase with
    | partData m =>
      cases m with
      | idx k =>
        have hkd : k < cx.dlen := by
          refine Nat.lt_of_not_le (fun h => h0 ?_)
          simp [Mp.runSpan, hp, h]
        obtain ⟨hn1, hn2, hn3, hinf⟩ := Mp.runSpan_spec cx mp b i stop' k hp hkd h0
        have hlift := foldl_pStep_run cx lim ((b.data.toList.drop i).take (Mp.runSpan cx mp b i stop'))
          ⟨mp, nFiles, nFields, curIsFile, sent, none⟩ out rfl (by
          intro y c hy
          have hpre : (Mp.D cx).take k ++ (y ++ [c]) <+: (Mp.D cx).take k ++ (b.data.toList.drop i).take (Mp.runSpan cx mp b i stop') :=
            (List.prefix_append_right_inj _).2 hy
          have hyc : (Mp.D cx).take k ++ y <+: (Mp.D cx).take k ++ (y ++ [c]) := ⟨[c], by simp⟩
          have hy1 := dataSize_feed_run cx mp k hp hkd y (fun h => hinf (h.trans (hyc.trans hpre).isInfix))
          have hy2 := dataSize_feed_run cx mp k hp hkd (y ++ [c]) (fun h => hinf (h.trans hpre.isInfix))
          refine ⟨hy1.1, hy2.1, fun hf => ?_⟩
          have hyl := hy.length_le
          simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop] at hyl
          have : stop' ≤ i + (lim.maxPartSize - (sent + mp.data.size + cx.dlen)) := by
            rw [← hst]; simp only at hf; simp [pStop, hf, Nat.min_le_right]
          simp only [List.length_append, List.length_singleton] at hy2
          have h5 := Mp.dlen_ge cx
          simp only at hf ⊢
          omega)
        rw [hlift]
        simp only [pBulk]
        rw [Mp.runBulk_eq]
        rfl
      | _ => simp [Mp.runSpan, hp] at h0
    | _ => simp [Mp.runSpan, hp] at h0

theorem pSpan_le (cx : Mp.Ctx) (lim : FormLimits) (r : PState × Array PartEvent) (b : ByteArray) (i stop : Nat) :
    pSpan cx lim r b i stop ≤ stop - i := by
  unfold pSpan
  split
  · exact Nat.zero_le _
  · by_cases h0 : Mp.runSpan cx r.1.mp b i (pStop cx lim r.1 i stop) = 0
    · omega
    · have hs : pStop cx lim r.1 i stop ≤ stop := by unfold pStop; split <;> omega
      cases hp : r.1.mp.phase with
      | partData m =>
        cases m with
        | idx k =>
          have hkd : k < cx.dlen := by
            refine Nat.lt_of_not_le (fun h => h0 ?_)
            simp [Mp.runSpan, hp, h]
          have := (Mp.runSpan_spec cx r.1.mp b i _ k hp hkd h0).2.2.1
          omega
        | _ => simp [Mp.runSpan, hp] at h0
      | _ => simp [Mp.runSpan, hp] at h0

/-- A chunk, with the shortcuts, is the fold of `pStep` over its bytes. -/
theorem pChunk_eq (cx : Mp.Ctx) (lim : FormLimits) (chunk : ByteArray) (r : PState × Array PartEvent) :
    pChunk cx lim chunk r = chunk.data.toList.foldl (pStep cx lim) r := by
  unfold pChunk
  rw [bytesFoldRun_eq (pStep cx lim) (pSpan cx lim) (pBulk cx) (fun r => r.1.halted)
    (fun r c h => pStep_halted cx lim r c h) (pSpan_le cx lim) (pBulk_eq cx lim) chunk chunk.size _ 0 r rfl,
    bytesFold_full]

/-! ## The invariant -/

theorem partOf_info (hs : List (ByteArray × ByteArray)) (n : Bytes) (f : Option Bytes) (body : ByteArray)
    (h : dispositionParams hs = (some n, f)) :
    partOf ⟨hs, body⟩ = .ok ((PartInfo.ofHeaders hs n f).toPart body) := by
  unfold partOf
  simp [h, PartInfo.ofHeaders, PartInfo.toPart]; rfl

theorem partOf_body {hs : List (ByteArray × ByteArray)} {b : ByteArray} {x : StarlettePart}
    (h : partOf ⟨hs, b⟩ = .ok x) (b' : ByteArray) : partOf ⟨hs, b'⟩ = .ok { x with data := b' } ∧ x.data = b := by
  unfold partOf at h ⊢
  simp only at h ⊢
  split at h
  · cases h; simp_all; rfl
  · cases h

theorem mapM_push {l : List RawPart} {r : List StarlettePart} {p : RawPart} {x : StarlettePart}
    (h1 : l.mapM partOf = .ok r) (h2 : partOf p = .ok x) : (l ++ [p]).mapM partOf = .ok (r ++ [x]) := by
  rw [List.mapM_append, h1, List.mapM_cons, List.mapM_nil, h2]; rfl

namespace MultipartStream

theorem events_append (c : Collector) (a b : Array PartEvent) : c.events (a ++ b) = (c.events a).events b := by
  simp [Collector.events]

@[simp] theorem events_empty (c : Collector) : c.events #[] = c := rfl

@[simp] theorem events_push (c : Collector) (a : Array PartEvent) (e : PartEvent) :
    c.events (a.push e) = (c.events a).event e := by
  simp [Collector.events]

end MultipartStream

open MultipartStream in
/-- The invariant between the whole-buffer state `W`, the streaming state
`P` and the parts assembled from the events `C`: the same error; and while
there is none, python-multipart's streaming invariant with some collector
`C0` of its events, the same counters, the completed parts are `C0`'s, and
in part data the current part is `C0`'s with `P.sent` of its bytes reported. -/
structure SInv (W : MpState) (P : PState) (C : Collector) : Prop where
  err : W.err = P.err
  ok : W.err = none → ∃ C0 : MultipartParser.Collector, MultipartParser.Inv W.inner P.mp C0 ∧
    W.nFiles = P.nFiles ∧ W.nFields = P.nFields ∧ W.curIsFile = P.curIsFile ∧
    C0.done.toList.mapM partOf = .ok C.done.toList ∧
    (Mp.InData W.inner → partOf ⟨C0.headers.toList, C0.body⟩ = .ok C.cur ∧ P.sent = C0.body.size)

theorem sinv_init : SInv {} {} {} :=
  ⟨rfl, fun _ => ⟨{}, ⟨rfl, rfl, trivial⟩, rfl, rfl, rfl, rfl, fun ⟨_, h⟩ => by cases h⟩⟩

theorem halted_eq {W : MpState} {P : PState} {C : MultipartStream.Collector} (h : SInv W P C) :
    mpHalted W = P.halted := by
  unfold mpHalted PState.halted
  rw [h.err]
  cases he : P.err with
  | some e => rfl
  | none =>
    obtain ⟨C0, hI, -⟩ := h.ok (h.err.trans he)
    have := (MultipartParser.forget_eq hI.1).1
    simp only [Option.isSome_none, Bool.false_or]
    rw [this]
    cases P.mp.phase <;> rfl

/-! ### The transitions, on both sides -/

/-- The headers end: Starlette's checks on the part's name and kind. -/
def onHeaders (lim : FormLimits) (hs : List (ByteArray × ByteArray)) (nFiles nFields : Nat) :
    Option LimitError × Bool × Option PartInfo :=
  match dispositionParams hs with
  | (none, _) => (some .missingName, false, none)
  | (some n, some f) =>
    if lim.maxFiles < nFiles + 1 then (some (.tooManyFiles lim.maxFiles), false, none)
    else (none, true, some (PartInfo.ofHeaders hs n (some f)))
  | (some n, none) =>
    if lim.maxFields < nFields + 1 then (some (.tooManyFields lim.maxFields), false, none)
    else (none, false, some (PartInfo.ofHeaders hs n none))

theorem mpStep_A (cx : Mp.Ctx) (lim : FormLimits) (W : MpState) (c : UInt8) (hh : mpHalted W = false)
    (he : W.err = none) (hA : W.inner.phase = .headersAlmostDone) {m : DelimMatch}
    (hA' : (Mp.step cx W.inner c).phase = .partData m) :
    mpStep cx lim W c =
      match onHeaders lim (Mp.step cx W.inner c).headers.toList W.nFiles W.nFields with
      | (some e, _, _) => { W with inner := Mp.step cx W.inner c, err := some e }
      | (none, true, _) => { W with inner := Mp.step cx W.inner c, nFiles := W.nFiles + 1, curIsFile := true }
      | (none, false, _) => { W with inner := Mp.step cx W.inner c, nFields := W.nFields + 1, curIsFile := false } := by
  unfold mpStep onHeaders
  simp only [hh, he, hA, hA', Bool.false_eq_true, ↓reduceIte]
  split <;> (try split) <;> simp_all

theorem pStep_A (cx : Mp.Ctx) (lim : FormLimits) (P : PState) (out : Array PartEvent) (c : UInt8)
    (hh : P.halted = false) (hA : P.mp.phase = .headersAlmostDone) {m : DelimMatch}
    (hA' : (Mp.step cx P.mp c).phase = .partData m) :
    pStep cx lim (P, out) c =
      match onHeaders lim (Mp.step cx P.mp c).headers.toList P.nFiles P.nFields with
      | (some e, _, _) => ({ P with mp := Mp.step cx P.mp c, err := some e }, out)
      | (none, true, i) => ({ P with mp := Mp.step cx P.mp c, nFiles := P.nFiles + 1, curIsFile := true, sent := 0 },
          match i with | some i => out.push (.part i) | none => out)
      | (none, false, i) => ({ P with mp := Mp.step cx P.mp c, nFields := P.nFields + 1, curIsFile := false, sent := 0 },
          match i with | some i => out.push (.part i) | none => out) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := P
  have he : err = none := ((halted_iff _).1 hh).1
  subst he
  simp only at hA hA' hh ⊢
  unfold pStep onHeaders
  simp only [hh, Bool.false_eq_true, ↓reduceIte, MultipartParser.stepEv_headers_done cx mp #[] c hA hA', hA, hA']
  split <;> (try split) <;> simp_all [ofMpEvent, List.filterMap_cons, List.filterMap_nil]

theorem mpStep_B (cx : Mp.Ctx) (lim : FormLimits) (W : MpState) (c : UInt8) (hh : mpHalted W = false)
    (he : W.err = none) {m m' : DelimMatch} (hB : W.inner.phase = .partData m)
    (hB' : (Mp.step cx W.inner c).phase = .partData m') :
    mpStep cx lim W c =
      if (!W.curIsFile && decide (lim.maxPartSize < (Mp.step cx W.inner c).data.size)) = true then
        { W with inner := Mp.step cx W.inner c, err := some (.partTooLarge lim.maxPartSize) }
      else { W with inner := Mp.step cx W.inner c } := by
  unfold mpStep
  simp only [hh, he, hB, hB', Bool.false_eq_true, ↓reduceIte]

theorem pStep_B (cx : Mp.Ctx) (lim : FormLimits) (P : PState) (out : Array PartEvent) (c : UInt8)
    (hh : P.halted = false) {m m' : DelimMatch} (hB : P.mp.phase = .partData m)
    (hB' : (Mp.step cx P.mp c).phase = .partData m') :
    pStep cx lim (P, out) c =
      if (!P.curIsFile && decide (lim.maxPartSize < P.sent + (Mp.step cx P.mp c).data.size)) = true then
        ({ P with mp := Mp.step cx P.mp c, err := some (.partTooLarge lim.maxPartSize) }, out)
      else ({ P with mp := Mp.step cx P.mp c }, out) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := P
  have he : err = none := ((halted_iff _).1 hh).1
  subst he
  simp only at hB hB' hh ⊢
  unfold pStep
  simp only [hh, Bool.false_eq_true, ↓reduceIte, MultipartParser.stepEv_data_data cx mp #[] c hB hB', hB, hB',
    Array.isEmpty_empty]

theorem mpStep_other (cx : Mp.Ctx) (lim : FormLimits) (W : MpState) (c : UInt8) (hh : mpHalted W = false)
    (he : W.err = none) (h1 : ¬ (Mp.InData W.inner ∧ Mp.InData (Mp.step cx W.inner c)))
    (h2 : ¬ (W.inner.phase = .headersAlmostDone ∧ Mp.InData (Mp.step cx W.inner c))) :
    mpStep cx lim W c = { W with inner := Mp.step cx W.inner c } := by
  unfold mpStep
  simp only [hh, he, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hp hp'; exact absurd ⟨hp, _, hp'⟩ h2
  · rename_i hp hp'; exact absurd ⟨⟨_, hp⟩, _, hp'⟩ h1
  · rfl

theorem pStep_other (cx : Mp.Ctx) (lim : FormLimits) (P : PState) (out : Array PartEvent) (c : UInt8)
    (hh : P.halted = false) (h1 : ¬ (Mp.InData P.mp ∧ Mp.InData (Mp.step cx P.mp c)))
    (h2 : ¬ (P.mp.phase = .headersAlmostDone ∧ Mp.InData (Mp.step cx P.mp c))) :
    pStep cx lim (P, out) c =
      ({ P with mp := (MultipartParser.stepEv cx (P.mp, #[]) c).1 },
        if (MultipartParser.stepEv cx (P.mp, #[]) c).2.isEmpty then out
        else out ++ (MultipartParser.stepEv cx (P.mp, #[]) c).2.filterMap ofMpEvent) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := P
  have he : err = none := ((halted_iff _).1 hh).1
  subst he
  simp only at h1 h2 hh ⊢
  have hph : ((MultipartParser.stepEv cx (mp, #[]) c).1).phase = (Mp.step cx mp c).phase :=
    (MultipartParser.forget_eq (MultipartParser.stepEv_fst cx mp #[] c)).1
  unfold pStep
  simp only [hh, Bool.false_eq_true, ↓reduceIte]
  generalize hE : MultipartParser.stepEv cx (mp, #[]) c = E at hph ⊢
  obtain ⟨m', evs⟩ := E
  simp only at hph ⊢
  split
  · rename_i hp hp'; rw [hph] at hp'; exact absurd ⟨hp, _, hp'⟩ h2
  · rename_i hp hp'; rw [hph] at hp'; exact absurd ⟨⟨_, hp⟩, _, hp'⟩ h1
  · rfl

theorem forget_step (cx : Mp.Ctx) {W P : MState} (h : Mp.forget W = Mp.forget P) (c : UInt8) :
    Mp.forget (Mp.step cx W c) = Mp.forget (Mp.step cx P c) := by
  have a := (Mp.forgets cx).2 W c
  have b := (Mp.forgets cx).2 P c
  rw [h] at a
  exact a.symm.trans b

theorem forget_headers {W P : MState} (h : Mp.forget W = Mp.forget P) : W.headers = P.headers := by
  cases W; cases P; simp [Mp.forget] at h; simp [h]

theorem onHeaders_ok (lim : FormLimits) (hs : List (ByteArray × ByteArray)) (a b : Nat) (isF : Bool) (i : Option PartInfo)
    (h : onHeaders lim hs a b = (none, isF, i)) :
    ∃ n f, dispositionParams hs = (some n, f) ∧ i = some (PartInfo.ofHeaders hs n f) ∧ isF = f.isSome ∧
      (isF = true → ¬ lim.maxFiles < a + 1) ∧ (isF = false → ¬ lim.maxFields < b + 1) := by
  unfold onHeaders at h
  rcases hd : dispositionParams hs with ⟨_ | n, _ | f⟩ <;> rw [hd] at h <;> simp only at h
  · cases h
  · cases h
  · by_cases hl : lim.maxFields < b + 1
    · simp [hl] at h
    · simp only [hl, ↓reduceIte, Prod.mk.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨n, none, rfl, rfl, rfl, by simp, fun _ => hl⟩
  · by_cases hl : lim.maxFiles < a + 1
    · simp [hl] at h
    · simp only [hl, ↓reduceIte, Prod.mk.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨n, some f, rfl, rfl, rfl, fun _ => hl, by simp⟩

theorem filterMap_quiet (evs : Array MultipartEvent) (h : ∀ e ∈ evs, (∀ b, e ≠ .partData b) ∧ e ≠ .partEnd) :
    evs.filterMap ofMpEvent = #[] := by
  apply Array.ext'
  simp only [Array.toList_filterMap, List.filterMap_eq_nil_iff]
  intro e he
  have := h e (by simpa using he)
  cases e with
  | partData b => exact absurd rfl (this.1 b)
  | partEnd => exact absurd rfl this.2
  | _ => rfl

theorem filterMap_push_none (a : Array MultipartEvent) (x : MultipartEvent) (h : ofMpEvent x = none) :
    (a.push x).filterMap ofMpEvent = a.filterMap ofMpEvent := by
  apply Array.ext'
  simp [List.filterMap_append, h]

theorem byteArray_append_eq_empty {a b : ByteArray} (h : a ++ b = ByteArray.empty) : a = ByteArray.empty := by
  have h1 := congrArg (fun x : ByteArray => x.data.toList) h
  simp only [ByteArray.data_append, Array.toList_append, ByteArray.data_empty', Array.toList_empty] at h1
  have h2 : a.data.toList = [] := (List.append_eq_nil_iff.1 h1).1
  exact ByteArray.ext_toList (by rw [h2]; rfl)

theorem byteArray_append_empty (a : ByteArray) : a ++ ByteArray.empty = a :=
  ByteArray.ext_toList (by simp [ByteArray.data_append])

open MultipartStream in
theorem sinv_step (cx : Mp.Ctx) (lim : FormLimits) (W : MpState) (P : PState) (C : Collector) (c : UInt8)
    (h : SInv W P C) :
    SInv (mpStep cx lim W c) (pStep cx lim (P, #[]) c).1 (C.events (pStep cx lim (P, #[]) c).2) := by
  by_cases hh : P.halted = true
  · have hW : mpHalted W = true := (halted_eq h).trans hh
    rw [show mpStep cx lim W c = W from mpHalted_fix cx lim W c hW, pStep_halted cx lim _ c hh]
    exact h
  · have hh' : P.halted = false := by simpa using hh
    obtain ⟨hPe, hPf, hPd⟩ := (halted_iff P).1 hh'
    have hWe : W.err = none := h.err.trans hPe
    obtain ⟨C0, hI, hnF, hnFi, hcf, hdone, hcur⟩ := h.ok hWe
    have hWh : mpHalted W = false := (halted_eq h).trans hh'
    have hI' := MultipartParser.inv_step cx W.inner P.mp C0 c hI
    obtain ⟨hph, -⟩ := MultipartParser.forget_eq hI.1
    have hIJ := forget_step cx hI.1 c
    obtain ⟨hphIJ, -⟩ := MultipartParser.forget_eq hIJ
    have hhdIJ := forget_headers hIJ
    have hsp := Mp.step_parts cx W.inner c
    by_cases hA : W.inner.phase = .headersAlmostDone ∧ Mp.InData (Mp.step cx W.inner c)
    · -- the headers end
      obtain ⟨hA1, m, hm⟩ := hA
      have hP1 : P.mp.phase = .headersAlmostDone := hph ▸ hA1
      have hP2 : (Mp.step cx P.mp c).phase = .partData m := hphIJ ▸ hm
      have hEv := MultipartParser.stepEv_headers_done cx P.mp #[] c hP1 hP2
      rw [hEv] at hI'
      simp only [MultipartParser.events_append, MultipartParser.Collector.events, Array.foldl_push, Array.foldl_empty,
        MultipartParser.Collector.event] at hI'
      rw [mpStep_A cx lim W c hWh hWe hA1 hm, pStep_A cx lim P #[] c hh' hP1 hP2, ← hhdIJ, ← hnF, ← hnFi]
      have hdata : (Mp.step cx W.inner c).data = ByteArray.empty := by
        rcases hsp with ⟨_, h2⟩ | ⟨⟨m0, h0⟩, _, _⟩
        · rcases h2 ⟨m, hm⟩ with ⟨⟨m0, h0⟩, _⟩ | ⟨_, _, h3⟩
          · rw [hA1] at h0; cases h0
          · exact h3
        · rw [hA1] at h0; cases h0
      have hpi := hI'.2.2
      simp only [MultipartParser.PhaseInv, hm] at hpi
      obtain ⟨hhd, hbd⟩ := hpi
      rw [hdata] at hbd
      have hbody : C0.body = ByteArray.empty := byteArray_append_eq_empty hbd.symm
      cases hoh : onHeaders lim (Mp.step cx W.inner c).headers.toList W.nFiles W.nFields with
      | mk e rest =>
        obtain ⟨isF, i⟩ := rest
        cases e with
        | some e => exact ⟨rfl, fun h => by cases h⟩
        | none =>
          obtain ⟨n, f, hd, hi, hisF, _, _⟩ := onHeaders_ok lim _ _ _ isF i hoh
          subst hi
          cases isF <;>
          · refine ⟨by simp [hPe, hWe], fun _ => ⟨C0, hI', by simp [hnF], by simp [hnFi], by simp, ?_, fun _ => ?_⟩⟩
            · simpa [Collector.events, Collector.event] using hdone
            · simp only [Collector.events, Array.foldl_push, Array.foldl_empty, Collector.event]
              rw [hhd, hbody, partOf_info _ n f _ hd]
              exact ⟨rfl, by simp⟩
    · by_cases hin : Mp.InData W.inner
      · obtain ⟨m, hm⟩ := hin
        have hP1 : P.mp.phase = .partData m := hph ▸ hm
        by_cases hin' : Mp.InData (Mp.step cx W.inner c)
        · -- part data stays part data
          obtain ⟨m', hm'⟩ := hin'
          have hP2 : (Mp.step cx P.mp c).phase = .partData m' := hphIJ ▸ hm'
          rw [MultipartParser.stepEv_data_data cx P.mp #[] c hP1 hP2] at hI'
          simp only [MultipartParser.Collector.events, Array.foldl_empty] at hI'
          rw [mpStep_B cx lim W c hWh hWe hm hm', pStep_B cx lim P #[] c hh' hP1 hP2]
          have hpi := hI'.2.2
          simp only [MultipartParser.PhaseInv, hm'] at hpi
          obtain ⟨hc1, hsent⟩ := hcur ⟨m, hm⟩
          have hsz : (Mp.step cx W.inner c).data.size = P.sent + (Mp.step cx P.mp c).data.size := by
            rw [hpi.2, ByteArray.size_append, hsent]
          rw [hsz, hcf]
          split
          · exact ⟨rfl, fun h => by cases h⟩
          · exact ⟨by simp [hPe, hWe], fun _ => ⟨C0, hI', by simp [hnF], by simp [hnFi], by simp, by simpa using hdone,
              fun _ => ⟨by simpa using hc1, by simpa using hsent⟩⟩⟩
        · -- the part ends
          have h1 : ¬ (Mp.InData W.inner ∧ Mp.InData (Mp.step cx W.inner c)) := fun h => hin' h.2
          have h2 : ¬ (W.inner.phase = .headersAlmostDone ∧ Mp.InData (Mp.step cx W.inner c)) := fun h => hin' h.2
          have hin'P : ¬ Mp.InData (Mp.step cx P.mp c) := fun ⟨m', h⟩ => hin' ⟨m', hphIJ.trans h⟩
          rw [mpStep_other cx lim W c hWh hWe h1 h2,
            pStep_other cx lim P #[] c hh' (fun h => hin'P h.2) (fun h => hin'P h.2)]
          have hEv := MultipartParser.stepEv_leave cx P.mp #[] c hP1 hin'P
          rw [hEv] at hI' ⊢
          obtain ⟨-, hparts⟩ := MultipartParser.step_leave cx W.inner c hm hin'
          have hpi := hI.2.2
          simp only [MultipartParser.PhaseInv, hm] at hpi
          obtain ⟨hc1, hsent⟩ := hcur ⟨m, hm⟩
          obtain ⟨hcb, hcd⟩ := partOf_body hc1 (C0.body ++ P.mp.data)
          refine ⟨by simp [hPe, hWe], fun _ => ⟨_, hI', hnF, hnFi, hcf, ?_, fun h => absurd h hin'⟩⟩
          rw [hI'.2.1, hparts, Array.toList_push, ← hI.2.1, ← hpi.1, hpi.2]
          rw [mapM_push hdone hcb]
          have hX : ofMpEvent (if (Mp.step cx P.mp c).phase = .done then MultipartEvent.end else .partBegin) = none := by
            split <;> rfl
          rw [filterMap_push_none _ _ hX]
          simp only [MultipartParser.emitIf, Collector.events]
          split
          · rename_i hz
            have hz' : P.mp.data = ByteArray.empty := by
              have h0 : P.mp.data.data.size = 0 := by simpa using hz
              have h1 : P.mp.data.data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
              exact ByteArray.ext_toList (by rw [h1]; rfl)
            simp [List.filterMap_cons, ofMpEvent, Collector.event, hz', byteArray_append_empty, ← hcd, hX]
          · simp [List.filterMap_cons, ofMpEvent, Collector.event, hcd, hX]
      · -- outside part data, and not the end of the headers
        have hin' : ¬ Mp.InData (Mp.step cx W.inner c) := by
          intro h'
          rcases hsp with ⟨_, h2⟩ | ⟨h3, _⟩
          · rcases h2 h' with ⟨h4, _⟩ | ⟨h4, _⟩
            · exact hin h4
            · exact hA ⟨h4, h'⟩
          · exact hin h3
        have hinP : ¬ Mp.InData P.mp := fun ⟨m, h⟩ => hin ⟨m, hph.trans h⟩
        have hin'P : ¬ Mp.InData (Mp.step cx P.mp c) := fun ⟨m', h⟩ => hin' ⟨m', hphIJ.trans h⟩
        rw [mpStep_other cx lim W c hWh hWe (fun h => hin h.1) (fun h => hA h),
          pStep_other cx lim P #[] c hh' (fun h => hinP h.1) (fun h => hin'P h.2),
          filterMap_quiet _ (MultipartParser.stepEv_quiet cx P.mp c hinP)]
        have hparts : (Mp.step cx W.inner c).parts = W.inner.parts := by
          rcases hsp with ⟨h1, _⟩ | ⟨h3, _⟩
          · exact h1
          · exact absurd h3 hin
        refine ⟨by simp [hPe, hWe], fun _ => ⟨_, hI', hnF, hnFi, hcf, ?_, fun h => absurd h hin'⟩⟩
        rw [hI'.2.1, hparts, ← hI.2.1]
        split <;> simpa using hdone

theorem foldl_pStep_append (cx : Mp.Ctx) (lim : FormLimits) (l : Bytes) : ∀ (s : PState) (out : Array PartEvent),
    l.foldl (pStep cx lim) (s, out) = ((l.foldl (pStep cx lim) (s, #[])).1, out ++ (l.foldl (pStep cx lim) (s, #[])).2) := by
  induction l with
  | nil => intro s out; simp
  | cons c cs ih =>
    intro s out
    simp only [List.foldl_cons]
    rw [pStep_append cx lim s out c, ih, ih (pStep cx lim (s, #[]) c).1 (pStep cx lim (s, #[]) c).2]
    simp

open MultipartStream in
theorem sinv_fold (cx : Mp.Ctx) (lim : FormLimits) (l : Bytes) : ∀ (W : MpState) (P : PState) (C : Collector),
    SInv W P C →
    SInv (l.foldl (mpStep cx lim) W) (l.foldl (pStep cx lim) (P, #[])).1 (C.events (l.foldl (pStep cx lim) (P, #[])).2) := by
  induction l with
  | nil => intro W P C h; simpa using h
  | cons c cs ih =>
    intro W P C h
    simp only [List.foldl_cons]
    rw [foldl_pStep_append cx lim cs (pStep cx lim (P, #[]) c).1 (pStep cx lim (P, #[]) c).2, events_append]
    exact ih _ _ _ (sinv_step cx lim W P C c h)

theorem pFlush_append (s : PState) (out : Array PartEvent) :
    pFlush s out = ((pFlush s #[]).1, out ++ (pFlush s #[]).2) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only [pFlush]
  split <;> (try split) <;> simp_all

theorem pFlush_err (s : PState) (out : Array PartEvent) : (pFlush s out).1.err = s.err := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only [pFlush]; split <;> rfl

theorem pFlush_phase (s : PState) (out : Array PartEvent) : (pFlush s out).1.mp.phase = s.mp.phase := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only [pFlush]; split <;> rfl

theorem pFlush_mp (s : PState) (out : Array PartEvent) : (pFlush s out).1.mp = { s.mp with data := ByteArray.empty } := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only [pFlush]; split <;> rfl

theorem pFlush_data (s : PState) (out : Array PartEvent) {m : DelimMatch} (hm : s.mp.phase = .partData m) :
    pFlush s out = ({ s with mp := { s.mp with data := ByteArray.empty }, sent := s.sent + s.mp.data.size },
      if s.mp.data.size == 0 then out else out.push (.data s.mp.data)) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only at hm ⊢
  simp only [pFlush, hm]

theorem pFlush_other (s : PState) (out : Array PartEvent) (hm : ¬ Mp.InData s.mp) :
    pFlush s out = ({ s with mp := { s.mp with data := ByteArray.empty } }, out) := by
  obtain ⟨mp, nFiles, nFields, curIsFile, sent, err⟩ := s
  simp only at hm ⊢
  simp only [pFlush]
  split
  · rename_i m hm'; exact absurd ⟨m, hm'⟩ hm
  · rfl

theorem flush_data (s : MState) (evs : Array MultipartEvent) {m : DelimMatch} (hm : s.phase = .partData m) :
    MultipartParser.flush s evs = ({ s with data := ByteArray.empty }, MultipartParser.emitIf evs s.data .partData) := by
  unfold MultipartParser.flush
  split
  · rfl
  · rename_i h; exact absurd hm (h m)

theorem inv_clear {W P : MState} {C : MultipartParser.Collector} (h : MultipartParser.Inv W P C) (hp : ¬ Mp.InData P) :
    MultipartParser.Inv W { P with data := ByteArray.empty } C := by
  obtain ⟨hf, hd, hph⟩ := h
  have hp' : ¬ Mp.InData W := fun ⟨m, h⟩ => hp ⟨m, (MultipartParser.forget_eq hf).1 ▸ h⟩
  refine ⟨by simpa [Mp.forget] using hf, hd, ?_⟩
  unfold MultipartParser.PhaseInv at hph ⊢
  cases hw : W.phase with
  | partData m => exact absurd ⟨m, hw⟩ hp'
  | _ => simp only [hw] at hph ⊢ <;> exact hph

open MultipartStream in
theorem sinv_flush (W : MpState) (P : PState) (C : Collector) (h : SInv W P C) :
    SInv W (pFlush P #[]).1 (C.events (pFlush P #[]).2) := by
  refine ⟨h.err.trans (pFlush_err P #[]).symm, fun hWe => ?_⟩
  obtain ⟨C0, hI, hnF, hnFi, hcf, hdone, hcur⟩ := h.ok hWe
  have hph := (MultipartParser.forget_eq hI.1).1
  by_cases hin : Mp.InData P.mp
  · obtain ⟨m, hm⟩ := hin
    have hfl := MultipartParser.inv_flush W.inner P.mp C0 hI
    rw [flush_data P.mp #[] hm] at hfl
    obtain ⟨hc1, hsent⟩ := hcur ⟨m, hph ▸ hm⟩
    rw [pFlush_data P #[] hm]
    refine ⟨_, hfl, hnF, hnFi, hcf, ?_, fun _ => ?_⟩
    · simp only [MultipartParser.emitIf]
      split <;> simpa [MultipartParser.Collector.events, MultipartParser.Collector.event, Collector.events,
        Collector.event] using hdone
    · simp only [MultipartParser.emitIf]
      obtain ⟨hcb, hcd⟩ := partOf_body hc1 (C0.body ++ P.mp.data)
      split
      · rename_i hz
        have h0 : P.mp.data.data.size = 0 := by simpa using hz
        have h1 : P.mp.data.data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
        have hz' : P.mp.data = ByteArray.empty := ByteArray.ext_toList (by rw [h1]; rfl)
        simp [hz', byteArray_append_empty, hc1, hsent, MultipartParser.Collector.events]
      · simp only [MultipartParser.Collector.events, Collector.events, Array.foldl_push, Array.foldl_empty,
          MultipartParser.Collector.event, Collector.event]
        refine ⟨by rw [hcd]; simpa using hcb, ?_⟩
        simp [hsent, ByteArray.size_append]
  · have hfl := inv_clear hI hin
    have hin' : ¬ Mp.InData W.inner := fun ⟨m, h⟩ => hin ⟨m, hph ▸ h⟩
    rw [pFlush_other P #[] hin]
    exact ⟨C0, hfl, hnF, hnFi, hcf, by simpa using hdone, fun h => absurd h hin'⟩

theorem mpHalted_foldl (cx : Mp.Ctx) (lim : FormLimits) (W : MpState) (h : mpHalted W = true) (l : Bytes) :
    l.foldl (mpStep cx lim) W = W := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have : mpStep cx lim W c = W := mpHalted_fix cx lim W c h
    simp only [List.foldl_cons]; rw [this]; exact ih

open MultipartStream in
theorem collect_eq (cx : Mp.Ctx) (lim : FormLimits) (chunks : List ByteArray) : ∀ (W : MpState) (P : PState) (C : Collector),
    SInv W P C → P.err = none → (∀ e, P.mp.phase ≠ .failed e) →
    collect { cx, lim, st := P } C chunks = mpResult ((chunks.flatMap (·.data.toList)).foldl (mpStep cx lim) W) := by
  induction chunks with
  | nil =>
    intro W P C h he hf
    obtain ⟨C0, hI, -, -, -, hdone, -⟩ := h.ok (h.err.trans he)
    simp only [collect, List.flatMap_nil, List.foldl_nil, mpResult, h.err.trans he]
    rw [(MultipartParser.forget_eq hI.1).1]
    split
    · rename_i e hp; exact absurd hp (hf e)
    · rw [← hI.2.1, hdone]
  | cons chunk rest ih =>
    intro W P C h he hf
    have h1 := sinv_fold cx lim chunk.data.toList W P C h
    have hfeed : ({ cx, lim, st := P } : MultipartStream).feed chunk =
        let R := chunk.data.toList.foldl (pStep cx lim) (P, #[])
        let F := pFlush R.1 #[]
        match F.1.err with
        | some e => .error e
        | none => match F.1.mp.phase with
          | .failed _ => .error .invalidMultipart
          | _ => .ok ({ cx, lim, st := F.1 }, R.2 ++ F.2) := by
      simp only [feed, pChunk_eq]
      rw [pFlush_append]
      rfl
    simp only [collect, List.flatMap_cons, List.foldl_append]
    rw [hfeed]
    generalize hR : chunk.data.toList.foldl (pStep cx lim) (P, #[]) = R at h1 ⊢
    obtain ⟨R1, R2⟩ := R
    have h2 := sinv_flush _ R1 _ h1
    rw [← events_append] at h2
    simp only
    generalize hW1 : chunk.data.toList.foldl (mpStep cx lim) W = W1 at h1 h2 ⊢
    cases hse : (pFlush R1 #[]).1.err with
    | some e =>
      have hWe : W1.err = some e := h2.err.trans hse
      rw [mpHalted_foldl cx lim W1 (by simp [mpHalted, hWe])]
      simp [mpResult, hWe]
    | none =>
      have hWe : W1.err = none := h2.err.trans hse
      obtain ⟨C0, hI, -⟩ := h2.ok hWe
      have hph := (MultipartParser.forget_eq hI.1).1
      simp only
      by_cases hfail : ∃ e, (pFlush R1 #[]).1.mp.phase = .failed e
      · obtain ⟨e, hp⟩ := hfail
        rw [hp]
        rw [mpHalted_foldl cx lim W1 (by simp [mpHalted, hWe, hph, hp])]
        simp [mpResult, hWe, hph, hp]
      · have hm : (match (pFlush R1 #[]).1.mp.phase with
            | .failed _ => (Except.error .invalidMultipart : Except LimitError (MultipartStream × Array PartEvent))
            | _ => .ok ({ cx, lim, st := (pFlush R1 #[]).1 }, R2 ++ (pFlush R1 #[]).2)) =
            .ok ({ cx, lim, st := (pFlush R1 #[]).1 }, R2 ++ (pFlush R1 #[]).2) := by
          split
          · rename_i e hp; exact absurd ⟨e, hp⟩ hfail
          · rfl
        rw [hm]
        exact ih W1 _ _ h2 hse (fun e h => hfail ⟨e, h⟩)

end Starlette

/-! ## What the parser keeps between chunks -/

namespace Mp

theorem hdrInv_init (cx : Ctx) : HdrInv cx {} := by
  simp [HdrInv, inHeader, noHeader]

set_option maxHeartbeats 1000000 in
theorem hdrInv_step (cx : Ctx) (s : MState) (c : UInt8) (h : HdrInv cx s) : HdrInv cx (step cx s c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold HdrInv step
  cases hp : s.phase <;> simp only [hp, inHeader, noHeader] at h5 h6 <;>
    simp only [sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart, finishPart] <;>
    (repeat' split) <;>
    simp_all [inHeader, noHeader, ByteArray.size_push, Array.toList_push] <;>
    first
      | omega
      | exact ⟨h4, by omega⟩
      | (intro a b hab; rcases hab with hab | ⟨rfl, rfl⟩ <;> first | exact h4 _ _ hab | omega)

end Mp

namespace Starlette

theorem stepEv_parts (cx : Mp.Ctx) (s : MState) (c : UInt8) (h : s.parts = #[]) :
    (MultipartParser.stepEv cx (s, #[]) c).1.parts = #[] := by
  by_cases hl : Mp.InData s ∧ ¬ Mp.InData (Mp.step cx s c)
  · obtain ⟨⟨m, hm⟩, h'⟩ := hl
    rw [MultipartParser.stepEv_leave cx s #[] c hm h']
  · have hp : (Mp.step cx s c).parts = s.parts := by
      rcases Mp.step_parts cx s c with ⟨h1, _⟩ | ⟨h1, h2, _⟩
      · exact h1
      · exact absurd ⟨h1, h2⟩ hl
    have hfst := MultipartParser.stepEv_fst cx s #[] c
    unfold Mp.forget at hfst
    simp only [MultipartParser.stepEv]
    split <;> simp [hp, h]

theorem stepEv_hdrInv (cx : Mp.Ctx) (s : MState) (c : UInt8) (h : Mp.HdrInv cx s) :
    Mp.HdrInv cx (MultipartParser.stepEv cx (s, #[]) c).1 := by
  have h' := Mp.hdrInv_step cx s c h
  simp only [MultipartParser.stepEv]
  split <;> exact h'

theorem pStep_retains (cx : Mp.Ctx) (lim : FormLimits) (r : PState × Array PartEvent) (c : UInt8)
    (h : r.1.mp.parts = #[] ∧ Mp.HdrInv cx r.1.mp) :
    (pStep cx lim r c).1.mp.parts = #[] ∧ Mp.HdrInv cx (pStep cx lim r c).1.mp := by
  obtain ⟨⟨mp, nFiles, nFields, curIsFile, sent, err⟩, out⟩ := r
  simp only at h
  have hp := stepEv_parts cx mp c h.1
  have hi := stepEv_hdrInv cx mp c h.2
  simp only [pStep]
  split
  · exact h
  · generalize MultipartParser.stepEv cx (mp, #[]) c = E at hp hi
    obtain ⟨m', evs⟩ := E
    simp only at hp hi ⊢
    split <;> (try split) <;> (try split) <;> exact ⟨hp, hi⟩

theorem foldl_pStep_retains (cx : Mp.Ctx) (lim : FormLimits) (l : Bytes) : ∀ (r : PState × Array PartEvent),
    r.1.mp.parts = #[] ∧ Mp.HdrInv cx r.1.mp →
    (l.foldl (pStep cx lim) r).1.mp.parts = #[] ∧ Mp.HdrInv cx (l.foldl (pStep cx lim) r).1.mp := by
  induction l with
  | nil => intro r h; exact h
  | cons c cs ih => intro r h; exact ih _ (pStep_retains cx lim r c h)

theorem new_retained (boundary : Boundary) (lim : FormLimits) : Retained (MultipartStream.new boundary lim) :=
  ⟨rfl, rfl, Mp.hdrInv_init _⟩

/-- **Memory.** Feeding a chunk keeps no part data and no completed part
between chunks, and the header buffers within the limits: what the parser
holds does not grow with the body. -/
theorem MultipartStream.feed_retains (p : MultipartStream) (chunk : ByteArray) (p' : MultipartStream)
    (evs : Array PartEvent) (hp : Retained p) (h : p.feed chunk = .ok (p', evs)) : Retained p' := by
  obtain ⟨cx, lim, st⟩ := p
  obtain ⟨_, hparts, hhdr⟩ := hp
  simp only at hparts hhdr
  have hpe : st.mp.parts = #[] := by
    apply Array.ext'; simp only [Array.toList_empty]; exact List.eq_nil_of_length_eq_zero (by simpa using hparts)
  have hr := foldl_pStep_retains cx lim chunk.data.toList (st, #[]) ⟨hpe, hhdr⟩
  simp only [MultipartStream.feed, pChunk_eq] at h
  generalize chunk.data.toList.foldl (pStep cx lim) (st, #[]) = R at hr h
  obtain ⟨R1, R2⟩ := R
  simp only at hr h
  have hFm := pFlush_mp R1 R2
  generalize pFlush R1 R2 = F at h hFm
  obtain ⟨F1, F2⟩ := F
  simp only at h hFm
  cases he : F1.err with
  | some e => rw [he] at h; cases h
  | none =>
    rw [he] at h
    simp only at h
    split at h
    · cases h
    · cases h
      refine ⟨by rw [hFm]; rfl, by rw [hFm]; simp [hr.1], ?_⟩
      rw [hFm]; exact hr.2

end Starlette

namespace Starlette.MultipartStream

/-- **Every chunking gives the whole-buffer result.** For a request with this
`Content-Type`, feeding the body to `MultipartStream` in any chunks and
assembling the parts from the events gives exactly Starlette's whole-buffer
parse (`parseMultipartRaw`): the same parts, or the same error. -/
theorem parseChunks_eq (lim : FormLimits) (contentType : ByteArray) (chunks : List ByteArray) :
    parseChunks lim contentType chunks = parseMultipartRaw lim contentType (concatChunks chunks) := by
  unfold parseChunks create parseMultipartRaw
  cases hb : boundaryParam contentType with
  | none => rfl
  | some b =>
    cases ho : Boundary.ofBytes? ⟨b.toArray⟩ with
    | none => simp only [ho]; rfl
    | some bd =>
      simp only [ho, bind, Except.bind, new, MultipartFormParser.write, MultipartFormParser.new, MultipartFormParser.finalize]
      rw [Machine.feedAUntil_eq _ (mpHalted_fix _ lim), Machine.feedA_eq]
      rw [collect_eq _ lim chunks {} {} {} sinv_init rfl (fun e h => by cases h)]
      simp [Machine.feedT, Machine.room, mpMachine, Machine.feed, concatChunks]
      rw [List.take_of_length_le]
      simp [List.length_flatMap]

end Starlette.MultipartStream

end LeanMultipart
