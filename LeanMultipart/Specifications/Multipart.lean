import LeanMultipart.RepoImpl.Form

/-!
# Specifications: multipart and forms
-/

namespace LeanMultipart.Spec

/-- The streaming multipart parser fed any chunking agrees with the
whole-buffer parser. -/
def MpStreamingAgrees (cx : Mp.Ctx) : Prop :=
  ∀ cs : List Bytes, Mp.result (Mp.feedChunks cx {} cs) = Mp.parseL cx cs.flatten

/-- The multipart parser is total. -/
def MpTotal (cx : Mp.Ctx) : Prop :=
  ∀ l, (Mp.parseL cx l).processed = Mp.room cx {} l.length ∧
    ∀ e, (Mp.parseL cx l).error = some e → e.offset < (Mp.parseL cx l).processed

/-- What `parseMultipart` promises about its result. -/
def MpParseSpec (cx : Mp.Ctx) (body : ByteArray) (r : MultipartResult) : Prop :=
  (∀ cs : List Bytes, cs.flatten = body.data.toList → Mp.result (Mp.feedChunks cx {} cs) = r) ∧
    r.processed ≤ body.size ∧ ∀ e, r.error = some e → e.offset < r.processed

/-- The form parser fed any chunking agrees with one write of the whole body. -/
def FormStreamingAgrees : Prop :=
  ∀ (p : FormParser) (cs : List ByteArray), cs.foldl FormParser.write p = p.write (FormParser.concat cs)

/-- Starlette's urlencoded limits hold of an accepted form. -/
def UrlencodedWithinLimits (lim : FormLimits) (fs : List QsField) : Prop :=
  fs.length ≤ lim.maxFields ∧ ∀ f ∈ fs, f.1.size + f.2.size ≤ lim.maxPartSize

/-- Starlette's multipart limits hold of an accepted form. -/
def MultipartWithinLimits (lim : FormLimits) (ps : List StarlettePart) : Prop :=
  (ps.filter (·.isFile)).length ≤ lim.maxFiles ∧ (ps.filter (! ·.isFile)).length ≤ lim.maxFields ∧
    ∀ p ∈ ps, p.isFile = false → p.data.size ≤ lim.maxPartSize

end LeanMultipart.Spec
