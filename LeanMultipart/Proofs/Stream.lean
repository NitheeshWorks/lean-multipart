import LeanMultipart.RepoImpl.QsStream
import LeanMultipart.RepoImpl.MpStream
import LeanMultipart.Proofs.MultipartStream

/-!
# The callback-style parsers run the whole-buffer machine

`QsParser` and `MultipartParser` forget what they have reported (completed
fields and parts, flushed name, value and data bytes). The machines'
control never reads those buffers, so forgetting commutes with stepping
(`Qs.forget_step`, `Mp.forget_step`). Hence the streaming parser's state,
for any chunking, is the whole-buffer state with those buffers cleared
(`QsParser.st_writeAll`, `MultipartParser.st_writeAll`): same phase, same
position, same error.
-/

namespace LeanMultipart

namespace Qs

/-- Clear the buffers the streaming parser does not keep. -/
def forget (s : QsState) : QsState := { s with fields := #[], name := #[], value := #[] }

@[simp] theorem forget_phase (s : QsState) : (forget s).phase = s.phase := rfl
@[simp] theorem forget_pos (s : QsState) : (forget s).pos = s.pos := rfl

theorem forget_step (cfg : QsConfig) (s : QsState) (c : UInt8) :
    forget (step cfg (forget s) c) = forget (step cfg s c) := by
  unfold step forget
  cases hp : s.phase <;> simp only [hp, nameByte, finishField] <;> (repeat' split) <;> simp_all

theorem forget_feed (cfg : QsConfig) (s : QsState) (l : Bytes) :
    forget (feed cfg (forget s) l) = forget (feed cfg s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [feed, List.foldl_cons] at *
    rw [← ih (step cfg (forget s) c), forget_step, ih]

theorem forget_feed_congr (cfg : QsConfig) {s t : QsState} (h : forget s = forget t) (l : Bytes) :
    forget (feed cfg s l) = forget (feed cfg t l) := by
  rw [← forget_feed, h, forget_feed]

end Qs

namespace QsParser

theorem stepEv_fst (cfg : QsConfig) (s : QsState) (evs : Array QsEvent) (c : UInt8) :
    Qs.forget (stepEv cfg (s, evs) c).1 = Qs.forget (Qs.step cfg s c) := by
  simp only [stepEv]
  split <;> simp [Qs.forget]

theorem fold_fst (cfg : QsConfig) (l : Bytes) :
    ∀ (s : QsState) (evs : Array QsEvent),
      Qs.forget (l.foldl (stepEv cfg) (s, evs)).1 = Qs.forget (Qs.feed cfg s l) := by
  induction l with
  | nil => intro s evs; rfl
  | cons c cs ih =>
    intro s evs
    simp only [List.foldl_cons]
    generalize hq : stepEv cfg (s, evs) c = q
    obtain ⟨t, evs'⟩ := q
    rw [ih t evs']
    have := stepEv_fst cfg s evs c
    rw [hq] at this
    exact (Qs.forget_feed_congr cfg this cs).trans (by simp [Qs.feed])

theorem flush_fst (s : QsState) (evs : Array QsEvent) : Qs.forget (flush s evs).1 = Qs.forget s := by
  unfold flush; split <;> simp [Qs.forget]

/-- One chunk: the streaming state is the whole-buffer state, forgotten. -/
theorem forget_writeSt (p : QsParser) (chunk : Bytes) :
    Qs.forget (p.writeSt chunk) = Qs.forget (Qs.feedT p.cfg p.st chunk) := by
  unfold writeSt Qs.feedT
  rw [flush_fst, fold_fst]

/-- Feed chunks one after another through the streaming parser (states only). -/
def writeAllSt (cfg : QsConfig) (st : QsState) : List Bytes → QsState
  | [] => st
  | c :: cs => writeAllSt cfg (writeSt { cfg, st } c) cs

/-- Any chunking: the streaming parser's state is the whole-buffer
machine's state with the reported buffers cleared, so phase, position and
error agree with `Qs.parse`. -/
theorem st_writeAll (cfg : QsConfig) (cs : List Bytes) :
    Qs.forget (writeAllSt cfg {} cs) = Qs.forget (Qs.feedT cfg {} cs.flatten) := by
  rw [← Qs.feedChunks_eq]
  suffices h : ∀ (s t : QsState), Qs.forget s = Qs.forget t →
      Qs.forget (writeAllSt cfg s cs) = Qs.forget (Qs.feedChunks cfg t cs) from h {} {} rfl
  induction cs with
  | nil => intro s t h; exact h
  | cons c cs ih =>
    intro s t h
    simp only [writeAllSt, Qs.feedChunks]
    apply ih
    rw [forget_writeSt]
    simp only [Qs.feedT, Qs.room]
    have hp : s.pos = t.pos := by rw [← Qs.forget_pos s, h]; rfl
    rw [hp]
    exact Qs.forget_feed_congr cfg h _

/-- `write` computes `writeSt`: on success the new state is it, and on
failure it has failed with the reported error. -/
theorem flush_st (s : QsState) (e1 e2 : Array QsEvent) :
    (flush s e1).1 = (flush s e2).1 := by
  unfold flush; split <;> rfl

theorem write_st (p : QsParser) (chunk : ByteArray) :
    (∀ q evs n, p.write chunk = .ok (q, evs, n) → q.st = p.writeSt chunk.data.toList) ∧
    (∀ e, p.write chunk = .error e → (p.writeSt chunk.data.toList).phase = .failed e.error) := by
  have hsz : chunk.size = chunk.data.toList.length := (Array.length_toList).symm
  have hf : (chunk.data.extract 0 (Qs.room p.cfg p.st chunk.size)).foldl (stepEv p.cfg) (p.st, #[]) =
      (chunk.data.toList.take (Qs.room p.cfg p.st chunk.data.toList.length)).foldl (stepEv p.cfg) (p.st, #[]) := by
    rw [← Array.foldl_toList, Array.toList_extract, hsz]
    simp only [List.extract, Nat.sub_zero, List.drop_zero]
  unfold write writeSt
  simp only []
  rw [hf]
  generalize List.foldl (stepEv p.cfg) (p.st, #[]) _ = acc
  obtain ⟨s0, ev0⟩ := acc
  rw [flush_st s0 #[] ev0]
  generalize flush s0 ev0 = fl
  obtain ⟨s1, ev1⟩ := fl
  simp only
  constructor
  · intro q evs n h
    split at h
    · cases h
    · cases h; rfl
  · intro e h
    split at h
    · rename_i e' he; cases h; exact he
    · cases h

end QsParser

namespace Mp

/-- Clear the buffers the streaming parser does not keep. -/
def forget (s : MState) : MState := { s with data := #[], parts := #[] }

@[simp] theorem forget_phase (s : MState) : (forget s).phase = s.phase := rfl
@[simp] theorem forget_pos (s : MState) : (forget s).pos = s.pos := rfl

theorem forget_step (cx : Ctx) (s : MState) (c : UInt8) :
    forget (step cx (forget s) c) = forget (step cx s c) := by
  unfold step forget
  cases hp : s.phase <;>
    simp only [hp, sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart,
      finishPart] <;> (repeat' split) <;> simp_all

theorem forget_feed (cx : Ctx) (s : MState) (l : Bytes) :
    forget (feed cx (forget s) l) = forget (feed cx s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [feed, List.foldl_cons] at *
    rw [← ih (step cx (forget s) c), forget_step, ih]

theorem forget_feed_congr (cx : Ctx) {s t : MState} (h : forget s = forget t) (l : Bytes) :
    forget (feed cx s l) = forget (feed cx t l) := by
  rw [← forget_feed, h, forget_feed]

end Mp

namespace MultipartParser

theorem stepEv_fst (cx : Mp.Ctx) (s : MState) (evs : Array MultipartEvent) (c : UInt8) :
    Mp.forget (stepEv cx (s, evs) c).1 = Mp.forget (Mp.step cx s c) := by
  simp only [stepEv]
  split <;> simp [Mp.forget]

theorem fold_fst (cx : Mp.Ctx) (l : Bytes) :
    ∀ (s : MState) (evs : Array MultipartEvent),
      Mp.forget (l.foldl (stepEv cx) (s, evs)).1 = Mp.forget (Mp.feed cx s l) := by
  induction l with
  | nil => intro s evs; rfl
  | cons c cs ih =>
    intro s evs
    simp only [List.foldl_cons]
    generalize hq : stepEv cx (s, evs) c = q
    obtain ⟨t, evs'⟩ := q
    rw [ih t evs']
    have := stepEv_fst cx s evs c
    rw [hq] at this
    exact (Mp.forget_feed_congr cx this cs).trans (by simp [Mp.feed])

theorem flush_fst (s : MState) (evs : Array MultipartEvent) : Mp.forget (flush s evs).1 = Mp.forget s := by
  unfold flush; split <;> simp [Mp.forget]

theorem forget_writeSt (p : MultipartParser) (chunk : Bytes) :
    Mp.forget (p.writeSt chunk) = Mp.forget (Mp.feedT p.cx p.st chunk) := by
  unfold writeSt Mp.feedT
  rw [flush_fst, fold_fst]

/-- Feed chunks one after another through the streaming parser (states only). -/
def writeAllSt (cx : Mp.Ctx) (st : MState) : List Bytes → MState
  | [] => st
  | c :: cs => writeAllSt cx (writeSt { cx, st } c) cs

/-- Any chunking: the streaming parser's state is the whole-buffer
machine's state with the reported buffers cleared. -/
theorem st_writeAll (cx : Mp.Ctx) (cs : List Bytes) :
    Mp.forget (writeAllSt cx {} cs) = Mp.forget (Mp.feedT cx {} cs.flatten) := by
  rw [← Mp.feedChunks_eq]
  suffices h : ∀ (s t : MState), Mp.forget s = Mp.forget t →
      Mp.forget (writeAllSt cx s cs) = Mp.forget (Mp.feedChunks cx t cs) from h {} {} rfl
  induction cs with
  | nil => intro s t h; exact h
  | cons c cs ih =>
    intro s t h
    simp only [writeAllSt, Mp.feedChunks]
    apply ih
    rw [forget_writeSt]
    simp only [Mp.feedT, Mp.room]
    have hp : s.pos = t.pos := by rw [← Mp.forget_pos s, h]; rfl
    rw [hp]
    exact Mp.forget_feed_congr cx h _

theorem flush_st (s : MState) (e1 e2 : Array MultipartEvent) :
    (flush s e1).1 = (flush s e2).1 := by
  unfold flush; split <;> rfl

theorem write_st (p : MultipartParser) (chunk : ByteArray) :
    (∀ q evs n, p.write chunk = .ok (q, evs, n) → q.st = p.writeSt chunk.data.toList) ∧
    (∀ e, p.write chunk = .error e → (p.writeSt chunk.data.toList).phase = .failed e.error) := by
  have hsz : chunk.size = chunk.data.toList.length := (Array.length_toList).symm
  have hf : (chunk.data.extract 0 (Mp.room p.cx p.st chunk.size)).foldl (stepEv p.cx) (p.st, #[]) =
      (chunk.data.toList.take (Mp.room p.cx p.st chunk.data.toList.length)).foldl (stepEv p.cx) (p.st, #[]) := by
    rw [← Array.foldl_toList, Array.toList_extract, hsz]
    simp only [List.extract, Nat.sub_zero, List.drop_zero]
  unfold write writeSt
  simp only []
  rw [hf]
  generalize List.foldl (stepEv p.cx) (p.st, #[]) _ = acc
  obtain ⟨s0, ev0⟩ := acc
  rw [flush_st s0 #[] ev0]
  generalize flush s0 ev0 = fl
  obtain ⟨s1, ev1⟩ := fl
  simp only
  constructor
  · intro q evs n h
    split at h
    · cases h
    · cases h; rfl
  · intro e h
    split at h
    · rename_i e' he; cases h; exact he
    · cases h

end MultipartParser

end LeanMultipart
