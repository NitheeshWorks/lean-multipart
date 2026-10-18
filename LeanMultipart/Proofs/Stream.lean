import LeanMultipart.RepoImpl.QsStream
import LeanMultipart.RepoImpl.MpStream
import LeanMultipart.Proofs.MultipartStream
import LeanMultipart.Proofs.ByteFacts

/-!
# The streaming parsers give the whole-buffer result

`QuerystringParser` and `MultipartParser` report fields and parts through
callbacks and forget what they have reported. The headline theorems say:
for every split of the input into chunks, collecting the callbacks the way
upstream's `FormParser` does gives exactly the whole-buffer result.

* `QuerystringParser.parseChunks_eq`:
  `QuerystringParser.parseChunks cfg chunks = Qs.parse cfg (concatChunks chunks)`.

The proof is an invariant between three things after the same bytes: the
whole-buffer machine state, the streaming parser's state, and what the
collector has assembled from the events.
-/

namespace LeanMultipart

namespace Qs

/-- Clear the buffers the streaming parser does not keep. -/
def forget (s : QsState) : QsState := { s with fields := #[], name := ByteArray.empty, value := ByteArray.empty }

theorem forgets (cfg : QsConfig) : (machine cfg).Forgets forget := by
  refine ⟨fun s => rfl, fun s c => ?_⟩
  show forget (step cfg (forget s) c) = forget (step cfg s c)
  unfold step forget
  cases hp : s.phase <;> simp only [nameByte, finishField] <;> (repeat' split) <;> simp_all

end Qs

namespace QuerystringParser

theorem emitIf_append (evs : Array QsEvent) (b : ByteArray) (mk : ByteArray → QsEvent) :
    emitIf evs b mk = evs ++ emitIf #[] b mk := by
  unfold emitIf; split <;> simp

/-- A step appends its events to those already there. -/
theorem stepEv_append (cfg : QsConfig) (s : QsState) (evs : Array QsEvent) (c : UInt8) :
    stepEv cfg (s, evs) c = ((stepEv cfg (s, #[]) c).1, evs ++ (stepEv cfg (s, #[]) c).2) := by
  simp only [stepEv]
  split <;> simp [emitIf_append (evs := evs)]

theorem foldl_stepEv_append (cfg : QsConfig) (l : Bytes) : ∀ (s : QsState) (evs : Array QsEvent),
    l.foldl (stepEv cfg) (s, evs) =
      ((l.foldl (stepEv cfg) (s, #[])).1, evs ++ (l.foldl (stepEv cfg) (s, #[])).2) := by
  induction l with
  | nil => intro s evs; simp
  | cons c cs ih =>
    intro s evs
    simp only [List.foldl_cons]
    rw [stepEv_append cfg s evs c, ih, ih (stepEv cfg (s, #[]) c).1 (stepEv cfg (s, #[]) c).2]
    simp

theorem flush_append (s : QsState) (evs : Array QsEvent) :
    flush s evs = ((flush s #[]).1, evs ++ (flush s #[]).2) := by
  unfold flush; split <;> simp [emitIf_append (evs := evs)]

theorem events_append (c : Collector) (a b : Array QsEvent) :
    c.events (a ++ b) = (c.events a).events b := by
  simp [Collector.events]

theorem stepEv_fst (cfg : QsConfig) (s : QsState) (evs : Array QsEvent) (c : UInt8) :
    Qs.forget (stepEv cfg (s, evs) c).1 = Qs.forget (Qs.step cfg s c) := by
  simp only [stepEv]
  split <;> simp [Qs.forget]

/-- The invariant: the streaming state is the whole-buffer state with
buffers forgotten, the collector has every completed field, and inside a
field the collector plus what the parser still holds is the whole-buffer
name and value. -/
def Inv (W P : QsState) (C : Collector) : Prop :=
  Qs.forget W = Qs.forget P ∧ C.done.toList = W.fields.toList ∧
  (W.phase = .fieldName → C.name.toList ++ P.name.toList = W.name.toList ∧ P.value = ByteArray.empty ∧
      C.value.toList = W.value.toList) ∧
  (W.phase = .fieldData → C.name.toList = W.name.toList ∧ P.name = ByteArray.empty ∧
      C.value.toList ++ P.value.toList = W.value.toList)

theorem forget_eq {W P : QsState} (h : Qs.forget W = Qs.forget P) :
    W.phase = P.phase ∧ W.pos = P.pos ∧ W.nameStart = P.nameStart := by
  cases W; cases P; simp [Qs.forget] at h; simp [h]

theorem ba_eq {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext_toList; simpa using h

theorem inv_step (cfg : QsConfig) (W P : QsState) (C : Collector) (c : UInt8) (h : Inv W P C) :
    Inv (Qs.step cfg W c) (stepEv cfg (P, #[]) c).1 (C.events (stepEv cfg (P, #[]) c).2) := by
  obtain ⟨hf, hd, hn, hv⟩ := h
  obtain ⟨hph, hpos, hns⟩ := forget_eq hf
  have hf' : Qs.forget (Qs.step cfg W c) = Qs.forget (Qs.step cfg P c) := by
    have a := (Qs.forgets cfg).2 W c
    have b := (Qs.forgets cfg).2 P c
    rw [hf] at a
    exact a.symm.trans b
  cases W with
  | mk wph wpos wns wn wv wf =>
  cases P with
  | mk pph ppos pns pn pv pf =>
  simp only at hph hpos hns hd hn hv
  subst hph hpos hns
  refine ⟨hf'.trans (stepEv_fst cfg _ _ c).symm, ?_⟩
  cases wph with
  | failed e => simp_all [Qs.step, stepEv, Collector.events]
  | beforeField fs =>
    by_cases hA : c = Byte.AMP
    · subst hA; cases fs <;> cases hs : cfg.strictParsing <;> simp_all [Qs.step, stepEv, Collector.events]
    · by_cases hE : c = Byte.EQ
      · subst hE
        simp_all [Qs.step, Qs.nameByte, stepEv, Collector.events, Collector.event]
      · simp_all [Qs.step, Qs.nameByte, stepEv, Collector.events, Collector.event]
  | fieldName =>
    obtain ⟨h1, h2, h3⟩ := hn rfl
    by_cases hA : c = Byte.AMP
    · subst hA; cases hs : cfg.strictParsing
      · simp_all [Qs.step, Qs.nameByte, Qs.finishField, stepEv, emitIf, Collector.events, Collector.event]
        split <;> simp_all [Collector.event] <;> (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
      · simp_all [Qs.step, Qs.nameByte, stepEv, Collector.events]
    · by_cases hE : c = Byte.EQ
      · subst hE
        simp_all [Qs.step, Qs.nameByte, stepEv, emitIf, Collector.events]
        split <;> simp_all [Collector.event] <;> (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all )))
      · simp_all [Qs.step, Qs.nameByte, stepEv, Collector.events]
        simp_all [← List.append_assoc]
  | fieldData =>
    obtain ⟨h1, h2, h3⟩ := hv rfl
    by_cases hA : c = Byte.AMP
    · subst hA
      simp_all [Qs.step, Qs.finishField, stepEv, emitIf, Collector.events, Collector.event]
      split <;> simp_all [Collector.event] <;> (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
    · simp_all [Qs.step, stepEv, Collector.events, Collector.event]
      simp_all [← List.append_assoc]

theorem inv_fold (cfg : QsConfig) (l : Bytes) : ∀ (W P : QsState) (C : Collector), Inv W P C →
    Inv (Qs.feed cfg W l) (l.foldl (stepEv cfg) (P, #[])).1 (C.events (l.foldl (stepEv cfg) (P, #[])).2) := by
  induction l with
  | nil => intro W P C h; simpa [Collector.events, Qs.feed] using h
  | cons c cs ih =>
    intro W P C h
    simp only [List.foldl_cons]
    rw [foldl_stepEv_append cfg cs (stepEv cfg (P, #[]) c).1 (stepEv cfg (P, #[]) c).2, events_append]
    exact ih _ _ _ (inv_step cfg W P C c h)

/-- The invariant at a chunk boundary: inside a field, the collector has
everything. -/
def Inv' (W P : QsState) (C : Collector) : Prop :=
  Inv W P C ∧ (W.phase = .fieldName ∨ W.phase = .fieldData →
    C.name.toList = W.name.toList ∧ C.value.toList = W.value.toList)

theorem inv_flush (W P : QsState) (C : Collector) (h : Inv W P C) :
    Inv' W (flush P #[]).1 (C.events (flush P #[]).2) := by
  obtain ⟨hf, hd, hn, hv⟩ := h
  obtain ⟨hph, _, _⟩ := forget_eq hf
  unfold flush
  split
  · rename_i hp
    have := hn (hph.trans hp)
    refine ⟨⟨by simpa [Qs.forget] using hf, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [emitIf] <;> (try split) <;> simp_all [Collector.events, Collector.event]
  · rename_i hp
    have := hv (hph.trans hp)
    refine ⟨⟨by simpa [Qs.forget] using hf, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [emitIf] <;> (try split) <;> simp_all [Collector.events, Collector.event]
  · rename_i h1 h2
    refine ⟨⟨hf, by simpa [Collector.events] using hd, fun h => absurd (hph ▸ h) h1,
      fun h => absurd (hph ▸ h) h2⟩, ?_⟩
    rintro (h | h)
    · exact absurd (hph ▸ h) h1
    · exact absurd (hph ▸ h) h2

theorem failed_feed (cfg : QsConfig) (s : QsState) (e : QsError) (h : s.phase = .failed e) (l : Bytes) :
    (Qs.feed cfg s l).phase = .failed e := by
  induction l generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (by simp [Qs.step, h])

theorem result_failed (s : QsState) (e : QsError) (h : s.phase = .failed e) : Qs.result s = .error e := by
  simp [Qs.result, Qs.finish, h]

theorem write_eq (cfg : QsConfig) (P : QsState) (chunk : ByteArray) :
    ({ cfg, st := P } : QuerystringParser).write chunk =
      let r := (chunk.data.toList.take (Qs.room cfg P chunk.data.toList.length)).foldl (stepEv cfg) (P, #[])
      let f := flush r.1 #[]
      match f.1.phase with
      | .failed e => .error ⟨e, (e.offset : Int) - P.pos⟩
      | _ => .ok ({ cfg, st := f.1 }, r.2 ++ f.2, Qs.room cfg P chunk.size) := by
  have hsz : chunk.size = chunk.data.toList.length := (Array.length_toList).symm
  unfold write
  simp only
  rw [bytesFold_take, ← hsz]
  generalize List.foldl (stepEv cfg) (P, #[]) _ = r
  obtain ⟨r1, r2⟩ := r
  rw [flush_append r1 r2]
  rfl

theorem go_eq (cfg : QsConfig) (chunks : List ByteArray) : ∀ (W P : QsState) (C : Collector), Inv' W P C →
    parseChunks.go { cfg, st := P } C chunks = Qs.result (Qs.feedT cfg W (chunks.flatMap (·.data.toList))) := by
  induction chunks with
  | nil =>
    intro W P C h
    obtain ⟨⟨hf, hd, _, _⟩, hin⟩ := h
    obtain ⟨hph, _, _⟩ := forget_eq hf
    simp only [parseChunks.go, List.flatMap_nil, Qs.feedT_nil]
    unfold finalize Qs.result Qs.finish
    simp only
    rw [← hph]
    cases hw : W.phase with
    | failed e => simp [hw]
    | fieldName =>
      obtain ⟨h1, h2⟩ := hin (Or.inl hw)
      simp [Collector.events, Collector.event, Qs.finishField, hd, ba_eq h1, ba_eq h2]
    | fieldData =>
      obtain ⟨h1, h2⟩ := hin (Or.inr hw)
      simp [Collector.events, Collector.event, Qs.finishField, hd, ba_eq h1, ba_eq h2]
    | beforeField b => simp [Collector.events, Collector.event, hd, hw]
  | cons chunk rest ih =>
    intro W P C h
    obtain ⟨hinv, _⟩ := h
    have hpos := (forget_eq hinv.1).2.1
    simp only [parseChunks.go, List.flatMap_cons]
    have hr : Qs.room cfg P chunk.data.toList.length = Qs.room cfg W chunk.data.toList.length := by
      simp [Qs.room, hpos]
    rw [write_eq, ← Qs.feedT_append, hr]
    have hfold := inv_fold cfg (chunk.data.toList.take (Qs.room cfg P chunk.data.toList.length)) W P C hinv
    have hfl := inv_flush _ _ _ hfold
    rw [hr] at hfl
    simp only
    generalize hR : List.foldl (stepEv cfg) (P, #[]) _ = R at hfl ⊢
    obtain ⟨r1, r2⟩ := R
    simp only at hfl ⊢
    have hW : Qs.feed cfg W (chunk.data.toList.take (Qs.room cfg W chunk.data.toList.length)) =
        Qs.feedT cfg W chunk.data.toList := rfl
    rw [hW] at hfl
    have hph := (forget_eq hfl.1.1).1
    rw [← events_append] at hfl
    cases hp : (flush r1 #[]).1.phase with
    | failed e =>
      simp only 
      rw [result_failed _ e (by
        show (Qs.feed cfg _ _).phase = _
        exact failed_feed cfg _ e (hph.trans hp) _)]
    | _ => simp only ; exact ih _ _ _ hfl

/-- **Streaming equals whole-buffer.** For every split of the input into
chunks, writing them to a `QuerystringParser`, finalizing, and collecting
the fields its callbacks report (as upstream's `FormParser` does) gives
exactly the whole-buffer parse. -/
theorem parseChunks_eq (cfg : QsConfig) (chunks : List ByteArray) :
    parseChunks cfg chunks = Qs.parse cfg (concatChunks chunks) := by
  unfold parseChunks
  have h0 : Inv' {} {} {} := by
    refine ⟨⟨rfl, rfl, ?_, ?_⟩, ?_⟩ <;> intro h <;> (try rcases h with h | h) <;> cases h
  rw [go_eq cfg chunks {} {} {} h0, Qs.parse_eq]
  simp [concatChunks, Qs.parseL]

end QuerystringParser

namespace Mp

/-- Clear the buffers the streaming parser does not keep. -/
def forget (s : MState) : MState := { s with data := ByteArray.empty, parts := #[] }

theorem forgets (cx : Ctx) : (machine cx).Forgets forget := by
  refine ⟨fun s => rfl, fun s c => ?_⟩
  show forget (step cx (forget s) c) = forget (step cx s c)
  unfold step forget
  cases hp : s.phase <;>
    simp only [sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart,
      finishPart] <;> (repeat' split) <;> simp_all

end Mp

namespace MultipartParser

theorem emitIf_append (evs : Array MultipartEvent) (b : ByteArray) (mk : ByteArray → MultipartEvent) :
    emitIf evs b mk = evs ++ emitIf #[] b mk := by
  unfold emitIf; split <;> simp

theorem stepEv_append (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) :
    stepEv cx (s, evs) c = ((stepEv cx (s, #[]) c).1, evs ++ (stepEv cx (s, #[]) c).2) := by
  simp only [stepEv]
  split <;> simp [emitIf_append (evs := evs)]

theorem foldl_stepEv_append (cx : Mp.Ctx) (l : Bytes) : ∀ (s : MState) (evs : Array MultipartEvent),
    l.foldl (stepEv cx) (s, evs) =
      ((l.foldl (stepEv cx) (s, #[])).1, evs ++ (l.foldl (stepEv cx) (s, #[])).2) := by
  induction l with
  | nil => intro s evs; simp
  | cons c cs ih =>
    intro s evs
    simp only [List.foldl_cons]
    rw [stepEv_append cx s evs c, ih, ih (stepEv cx (s, #[]) c).1 (stepEv cx (s, #[]) c).2]
    simp

theorem flush_append (s : MState) (evs : Array MultipartEvent) :
    flush s evs = ((flush s #[]).1, evs ++ (flush s #[]).2) := by
  unfold flush; split <;> simp [emitIf_append (evs := evs)]

theorem events_append (c : Collector) (a b : Array MultipartEvent) :
    c.events (a ++ b) = (c.events a).events b := by
  simp [Collector.events]

theorem stepEv_fst (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) :
    Mp.forget (stepEv cx (s, evs) c).1 = Mp.forget (Mp.step cx s c) := by
  simp only [stepEv]
  split <;> simp [Mp.forget]

/-- What the collector has, phase by phase. -/
def PhaseInv (W P : MState) (C : Collector) : Prop :=
  match W.phase with
  | .headerFieldStart | .headerValueAlmostDone | .headersAlmostDone =>
    C.headers = W.headers ∧ C.body = ByteArray.empty
  | .headerField => C.headers = W.headers ∧ C.body = ByteArray.empty ∧ C.hname = ByteArray.empty ∧ C.hvalue = ByteArray.empty
  | .headerValueStart | .headerValue =>
    C.headers = W.headers ∧ C.body = ByteArray.empty ∧ C.hname = W.name ∧ C.hvalue = ByteArray.empty
  | .partData _ => C.headers = W.headers ∧ W.data = C.body ++ P.data
  | _ => True

/-- The invariant: forgotten states agree, the collector has every
completed part, and the phase invariant. -/
def Inv (W P : MState) (C : Collector) : Prop :=
  Mp.forget W = Mp.forget P ∧ C.done.toList = W.parts.toList ∧ PhaseInv W P C

-- A case analysis over every phase of the multipart machine and every byte
-- class it distinguishes; each case is closed by `simp`.
set_option maxHeartbeats 2000000 in
theorem inv_step (cx : Mp.Ctx) (W P : MState) (C : Collector) (c : UInt8) (h : Inv W P C) :
    Inv (Mp.step cx W c) (stepEv cx (P, #[]) c).1 (C.events (stepEv cx (P, #[]) c).2) := by
  obtain ⟨hf, hd, hph⟩ := h
  have hf' : Mp.forget (Mp.step cx W c) = Mp.forget (Mp.step cx P c) := by
    have a := (Mp.forgets cx).2 W c
    have b := (Mp.forgets cx).2 P c
    rw [hf] at a
    exact a.symm.trans b
  refine ⟨hf'.trans (stepEv_fst cx _ _ c).symm, ?_⟩
  clear hf'
  cases W with
  | mk wph wpos whc whs wn wv wh wd wp =>
  cases P with
  | mk pph ppos phc phs pn pv ph pd pp =>
  simp only [Mp.forget, MState.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hf
  simp only at hd hph ⊢
  cases wph with
  | partData m =>
    cases m <;> simp only [PhaseInv] at hph <;>
      simp only [Mp.step, Mp.matchByte, Mp.restart, Mp.beginPart, Mp.finishPart, stepEv, emitIf, lastBody] <;>
      (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | start =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.sbByte, Mp.fail, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | preamble =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.sbByte, Mp.fail, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | startBoundary k =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.sbByte, Mp.fail, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | startBoundaryCR =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.fail, Mp.beginPart, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | endBoundary =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.fail, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | headerFieldStart =>
    simp only [PhaseInv] at hph
    by_cases hcr : c = Byte.CR
    · subst hcr; simp_all [Mp.step, stepEv, PhaseInv, Collector.events]
    · by_cases hn : cx.cfg.maxHeaderCount < whc + 1
      · simp_all [Mp.step, Mp.fail, stepEv, PhaseInv, Collector.events]
      · have e : Mp.step cx ⟨.headerFieldStart, wpos, whc, whs, wn, wv, wh, wd, wp⟩ c =
            Mp.headerFieldByte cx ⟨.headerFieldStart, wpos + 1, whc + 1, 0, ByteArray.empty, wv, wh, wd, wp⟩ c wpos := by
          simp [Mp.step, hcr, hn]
        have e' : Mp.step cx ⟨.headerFieldStart, wpos, whc, whs, wn, wv, wh, pd, pp⟩ c =
            Mp.headerFieldByte cx ⟨.headerFieldStart, wpos + 1, whc + 1, 0, ByteArray.empty, wv, wh, pd, pp⟩ c wpos := by
          simp [Mp.step, hcr, hn]
        simp only [stepEv, e, e']
        unfold Mp.headerFieldByte
        (repeat' split) <;> simp_all [Mp.fail, PhaseInv, Collector.events, Collector.event] <;>
          (repeat' split) <;> simp_all 
  | headerField =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.headerFieldByte, Mp.fail, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | headerValueStart =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.headerValueByte, Mp.fail, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | headerValue =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.headerValueByte, Mp.fail, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | headerValueAlmostDone =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.fail, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | headersAlmostDone =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, Mp.fail, stepEv, emitIf]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events, Collector.event] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | done =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))
  | failed e =>
    simp only [PhaseInv] at hph
    simp only [Mp.step, stepEv]
    (repeat' split) <;> simp_all [PhaseInv, Collector.events] <;>
      (try ((try (refine ⟨?_, ?_⟩)) <;> first | rfl | (apply ByteArray.ext_toList; simp_all [ByteArray.data_append]) | (apply Array.ext'; simp_all [ByteArray.data_append])))

theorem forget_eq {W P : MState} (h : Mp.forget W = Mp.forget P) : W.phase = P.phase ∧ W.pos = P.pos := by
  cases W; cases P; simp [Mp.forget] at h; simp [h]

theorem inv_fold (cx : Mp.Ctx) (l : Bytes) : ∀ (W P : MState) (C : Collector), Inv W P C →
    Inv (Mp.feed cx W l) (l.foldl (stepEv cx) (P, #[])).1 (C.events (l.foldl (stepEv cx) (P, #[])).2) := by
  induction l with
  | nil => intro W P C h; simpa [Collector.events, Mp.feed] using h
  | cons c cs ih =>
    intro W P C h
    simp only [List.foldl_cons]
    rw [foldl_stepEv_append cx cs (stepEv cx (P, #[]) c).1 (stepEv cx (P, #[]) c).2, events_append]
    exact ih _ _ _ (inv_step cx W P C c h)

theorem inv_flush (W P : MState) (C : Collector) (h : Inv W P C) :
    Inv W (flush P #[]).1 (C.events (flush P #[]).2) := by
  obtain ⟨hf, hd, hph⟩ := h
  obtain ⟨hp, _⟩ := forget_eq hf
  unfold flush
  split
  · rename_i m hm
    refine ⟨by simpa [Mp.forget] using hf, ?_, ?_⟩
    · simp only [emitIf]; split <;> simp_all [Collector.events, Collector.event] <;> rfl
    · unfold PhaseInv at hph ⊢
      rw [hp, hm] at hph ⊢
      simp only [emitIf]; split <;> simp_all [Collector.events, Collector.event]
  · exact ⟨hf, by simpa [Collector.events] using hd, by simpa [Collector.events] using hph⟩

theorem failed_feed (cx : Mp.Ctx) (s : MState) (e : MultipartError) (h : s.phase = .failed e) (l : Bytes) :
    (Mp.feed cx s l).phase = .failed e := by
  induction l generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (by simp [Mp.step, h])

theorem write_eq (cx : Mp.Ctx) (P : MState) (chunk : ByteArray) :
    ({ cx, st := P } : MultipartParser).write chunk =
      let r := (chunk.data.toList.take (Mp.room cx P chunk.data.toList.length)).foldl (stepEv cx) (P, #[])
      let f := flush r.1 #[]
      match f.1.phase with
      | .failed e => .error ⟨e, (e.offset : Int) - P.pos⟩
      | _ => .ok ({ cx, st := f.1 }, r.2 ++ f.2, Mp.room cx P chunk.size) := by
  have hsz : chunk.size = chunk.data.toList.length := (Array.length_toList).symm
  unfold write
  simp only
  rw [foldChunk_eq, bytesFold_take, ← hsz]
  generalize List.foldl (stepEv cx) (P, #[]) _ = r
  obtain ⟨r1, r2⟩ := r
  rw [flush_append r1 r2]
  rfl

theorem go_eq (cx : Mp.Ctx) (chunks : List ByteArray) : ∀ (W P : MState) (C : Collector), Inv W P C →
    (∀ e, W.phase ≠ .failed e) →
    parseChunks.go { cx, st := P } C chunks = (Mp.result (Mp.feedT cx W (chunks.flatMap (·.data.toList)))).toExcept := by
  induction chunks with
  | nil =>
    intro W P C h hnf
    simp only [parseChunks.go, List.flatMap_nil, Mp.feedT_nil, MultipartResult.toExcept, Mp.result]
    cases hw : W.phase with
    | failed e => exact absurd hw (hnf e)
    | _ => simp [h.2.1]
  | cons chunk rest ih =>
    intro W P C h _
    have hpos := (forget_eq h.1).2
    simp only [parseChunks.go, List.flatMap_cons]
    have hr : Mp.room cx P chunk.data.toList.length = Mp.room cx W chunk.data.toList.length := by
      simp [Mp.room, hpos]
    rw [write_eq, ← Mp.feedT_append, hr]
    have hfold := inv_fold cx (chunk.data.toList.take (Mp.room cx P chunk.data.toList.length)) W P C h
    have hfl := inv_flush _ _ _ hfold
    rw [hr] at hfl
    simp only
    generalize hR : List.foldl (stepEv cx) (P, #[]) _ = R at hfl ⊢
    obtain ⟨r1, r2⟩ := R
    simp only at hfl ⊢
    have hW : Mp.feed cx W (chunk.data.toList.take (Mp.room cx W chunk.data.toList.length)) =
        Mp.feedT cx W chunk.data.toList := rfl
    rw [hW] at hfl
    have hph := (forget_eq hfl.1).1
    rw [← events_append] at hfl
    cases hp : (flush r1 #[]).1.phase with
    | failed e =>
      simp only 
      have hfe : (Mp.feedT cx (Mp.feedT cx W chunk.data.toList) (rest.flatMap (·.data.toList))).phase = .failed e :=
        failed_feed cx _ e (hph.trans hp) _
      simp [MultipartResult.toExcept, Mp.result, hfe]
    | _ => simp only ; exact ih _ _ _ hfl (fun e he => by rw [hph, hp] at he; cases he)

/-- **Streaming equals whole-buffer.** For every split of the input into
chunks, writing them to a `MultipartParser` and collecting the parts its
callbacks report (as upstream's `FormParser` does) gives exactly the parts
of the whole-buffer parse, or its error. -/
theorem parseChunks_eq (cx : Mp.Ctx) (chunks : List ByteArray) :
    parseChunks cx chunks = (Mp.parse cx (concatChunks chunks)).toExcept := by
  unfold parseChunks
  rw [go_eq cx chunks {} {} {} ⟨rfl, rfl, trivial⟩ (fun e h => by cases h), Mp.parse_eq]
  simp [concatChunks, Mp.parseL]

end MultipartParser

end LeanMultipart
