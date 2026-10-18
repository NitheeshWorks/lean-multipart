import LeanMultipart.RepoImpl

/-!
# Specifications: multipart and forms
-/

namespace LeanMultipart.Mp

/-- A header the printer can write and the parser reads back: a non-empty
token name, a value with no `CR` that does not start with a space, and a
line within `maxHeaderSize` (name, colon, space and value). -/
def WFHeader (cfg : MultipartConfig) (h : ByteArray × ByteArray) : Prop :=
  h.1.data.toList ≠ [] ∧ (∀ c ∈ h.1.data.toList, Byte.isTokenChar c = true) ∧
    (∀ c ∈ h.2.data.toList, c ≠ Byte.CR) ∧ h.2.data.toList.head? ≠ some Byte.SPACE ∧
    h.1.data.toList.length + 2 + h.2.data.toList.length ≤ cfg.maxHeaderSize

/-- A part the printer can write and the parser reads back: at most
`maxHeaderCount` well-formed headers, and a body that does not contain the
delimiter. -/
def WFPart (cx : Ctx) (p : RawPart) : Prop :=
  p.headers.length ≤ cx.cfg.maxHeaderCount ∧ (∀ h ∈ p.headers, WFHeader cx.cfg h) ∧
    ¬ cx.boundary.delimL <:+: p.body.data.toList

/-- The size condition of the round trip. -/
def Fits (cx : Ctx) (ps : List RawPart) : Prop :=
  ∀ m, cx.cfg.maxSize = some m → (printL cx.boundary ps).length ≤ m

end LeanMultipart.Mp

namespace LeanMultipart.Starlette

/-- The invariant of the urlencoded limit machine. -/
def UrlInv (lim : FormLimits) (s : UrlState) : Prop :=
  s.err = none → s.inner.fields.size ≤ lim.maxFields ∧
    (∀ f ∈ s.inner.fields.toList, f.1.size + f.2.size ≤ lim.maxPartSize) ∧
    s.inner.name.size + s.inner.value.size ≤ lim.maxPartSize

/-- Whether a part is a file (its `Content-Disposition` has a `filename`). -/
def isFileRaw (p : RawPart) : Bool := (dispositionParams p.headers).2.isSome

/-- The phase is part data. -/
def inData (s : MState) : Bool := match s.phase with | .partData _ => true | _ => false

/-- The invariant of the multipart limit machine: while no limit error has
been raised, at most `max_files` files and `max_fields` fields have been
counted, the parts read and the part being read are accounted for in those
counts, and every field (read or being read) is within `max_part_size`. -/
def MpInv (lim : FormLimits) (s : MpState) : Prop :=
  s.err = none →
    s.nFiles ≤ lim.maxFiles ∧ s.nFields ≤ lim.maxFields ∧
    (∀ p ∈ s.inner.parts.toList, isFileRaw p = false → p.body.size ≤ lim.maxPartSize) ∧
    (inData s.inner = true → s.curIsFile = (dispositionParams s.inner.headers.toList).2.isSome ∧
      (s.curIsFile = false → s.inner.data.size ≤ lim.maxPartSize)) ∧
    (s.inner.parts.toList.filter isFileRaw).length + (inData s.inner && s.curIsFile).toNat ≤ s.nFiles ∧
    (s.inner.parts.toList.filter (! isFileRaw ·)).length + (inData s.inner && !s.curIsFile).toNat ≤ s.nFields

end LeanMultipart.Starlette

namespace LeanMultipart.Spec

/-- The multipart round trip: well-formed parts, printed and followed by any
epilogue, parse back to exactly themselves. -/
def MultipartRoundTrip (cx : Mp.Ctx) : Prop :=
  ∀ (ps : List RawPart) (epi : ByteArray), (∀ p ∈ ps, Mp.WFPart cx p) → Mp.Fits cx ps →
    (Mp.parse cx (Mp.print cx.boundary ps ++ epi)).toExcept = .ok ps

/-- The streaming `MultipartParser`, fed any split of the input and its
callbacks collected, gives the whole-buffer parts (or error). -/
def MpStreamingAgrees (cx : Mp.Ctx) : Prop :=
  ∀ chunks : List ByteArray, MultipartParser.parseChunks cx chunks = (Mp.parse cx (concatChunks chunks)).toExcept

/-- The multipart parser is total. -/
def MpTotal (cx : Mp.Ctx) : Prop :=
  ∀ l, (Mp.parseL cx l).processed = Mp.room cx {} l.length ∧
    ∀ e, (Mp.parseL cx l).error = some e → e.offset < (Mp.parseL cx l).processed

/-- What `parseMultipart` promises about its result. -/
def MpParseSpec (cx : Mp.Ctx) (body : ByteArray) (r : MultipartResult) : Prop :=
  (∀ chunks : List ByteArray, concatChunks chunks = body → MultipartParser.parseChunks cx chunks = r.toExcept) ∧
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

/-- Starlette's streaming parsers fed any chunking give the result of one
write of the whole body. -/
def StarletteStreamingAgrees : Prop :=
  (∀ (p : Starlette.UrlencodedParser) (cs : List ByteArray),
    (cs.foldl Starlette.UrlencodedParser.write p).finalize = (p.write (concatChunks cs)).finalize) ∧
  (∀ (p : Starlette.MultipartFormParser) (cs : List ByteArray),
    (cs.foldl Starlette.MultipartFormParser.write p).finalize = (p.write (concatChunks cs)).finalize)

/-- The limits are enforced as the bytes arrive: while no error has been
raised, the parser's state is within `max_fields`, `max_files` and
`max_part_size`. -/
def StarletteBounded : Prop :=
  (∀ lim body, Starlette.UrlInv lim ((({ lim } : Starlette.UrlencodedParser)).write body).st) ∧
  (∀ b lim body, Starlette.MpInv lim ((Starlette.MultipartFormParser.new b lim).write body).st)

end LeanMultipart.Spec
