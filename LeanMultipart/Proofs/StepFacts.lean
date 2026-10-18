import LeanMultipart.Proofs.MultipartStream
import LeanMultipart.Proofs.Querystring

/-!
# How a step changes what the machines retain

Facts used by the limit proofs: a querystring step adds at most one field,
the one it was reading; a multipart step adds at most one part, the one it
was reading, exactly when it leaves part data, and enters part data only
from the end of the headers (with empty data) or from part data (with the
same headers).
-/

namespace LeanMultipart

namespace Qs

theorem step_fields (cfg : QsConfig) (s : QsState) (c : UInt8) :
    (step cfg s c).fields = s.fields ∨ (step cfg s c).fields = s.fields.push (s.name, s.value) := by
  unfold step
  cases hp : s.phase <;> simp only [nameByte, finishField] <;> (repeat' split) <;> simp_all

theorem finish_fields (s : QsState) :
    (finish s).fields = s.fields ∨ (finish s).fields = s.fields.push (s.name, s.value) := by
  unfold finish; split <;> simp [finishField]

end Qs

namespace Mp

/-- The phase is part data. -/
def InData (s : MState) : Prop := ∃ m, s.phase = .partData m

/-- What one multipart step does to the retained parts and headers. -/
theorem step_parts (cx : Ctx) (s : MState) (c : UInt8) :
    ((step cx s c).parts = s.parts ∧
      (InData (step cx s c) →
        (InData s ∧ (step cx s c).headers = s.headers) ∨
        (s.phase = .headersAlmostDone ∧ (step cx s c).headers = s.headers ∧ (step cx s c).data = ByteArray.empty))) ∨
    (InData s ∧ ¬ InData (step cx s c) ∧ (step cx s c).parts = s.parts.push ⟨s.headers.toList, s.data⟩) := by
  unfold step InData
  cases hp : s.phase <;>
    simp only [sbByte, headerFieldByte, headerValueByte, matchByte, restart, fail, beginPart,
      finishPart] <;> (repeat' split) <;> simp_all

end Mp
end LeanMultipart
