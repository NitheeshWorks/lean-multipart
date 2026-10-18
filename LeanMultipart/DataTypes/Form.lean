import LeanMultipart.DataTypes.Multipart
import LeanMultipart.DataTypes.Querystring

/-!
# Form types

What upstream's `FormParser` hands to its `on_field` / `on_file` callbacks,
as data, and the limits Starlette's form parsers apply.

Upstream's `File` spools to memory or a temporary file; here a file's data
is held in memory (`FormFile.data`). The `UPLOAD_*` and
`MAX_MEMORY_FILE_SIZE` options are therefore excluded (see
`docs/traceability.toml`).
-/

namespace LeanMultipart

/-- Upstream's `Field`. `value = none` is a urlencoded field with no data
(`foo` or `foo=`); multipart fields always have a value. -/
structure FormField where
  name : ByteArray
  value : Option ByteArray
  contentType : Option ByteArray := none
  deriving Inhabited

/-- Upstream's `File`, held in memory. `fieldName` is `none` only for an
`application/octet-stream` body. -/
structure FormFile where
  fieldName : Option ByteArray
  fileName : Option ByteArray
  contentType : Option ByteArray := none
  headers : List (ByteArray × ByteArray) := []
  data : ByteArray
  deriving Inhabited

inductive FormItem where
  | field (f : FormField)
  | file (f : FormFile)
  deriving Inhabited

/-- `FormParser.DEFAULT_CONFIG`, minus the file-storage options. -/
structure FormParserConfig where
  maxBodySize : Option Nat := none
  maxHeaderCount : Nat := 8
  maxHeaderSize : Nat := 4096 + 128
  errorOnBadCte : Bool := false
  /-- Upstream rejects `MAX_BODY_SIZE < 1`. -/
  h_maxBodySize : ∀ m, maxBodySize = some m → 0 < m := by intro m h; cases h <;> decide

instance : Inhabited FormParserConfig := ⟨{}⟩

inductive DecodeErrorKind where
  | base64Padding
  | base64Leftover
  deriving DecidableEq, Repr, Inhabited

/-- Everything upstream's form layer can raise. -/
inductive FormError where
  | multipart (e : MultipartError)
  | querystring (e : QsError)
  /-- "No boundary given" -/
  | noBoundary
  /-- The boundary is not a `Boundary` (empty, too long, or a byte outside
  RFC 2046 `bchars`). -/
  | badBoundary
  /-- "Unknown Content-Type" -/
  | unknownContentType (ct : String)
  /-- "No Content-Type header given!" -/
  | noContentType
  /-- "Field name not found in Content-Disposition" -/
  | missingFieldName
  /-- "Unknown Content-Transfer-Encoding" (only with `errorOnBadCte`) -/
  | badCte (cte : ByteArray)
  /-- A base64 part did not decode. -/
  | decode (k : DecodeErrorKind)
  deriving Inhabited

/-- The limits of Starlette's `FormParser` / `MultiPartParser`
(`max_fields`, `max_files`, `max_part_size`), with Starlette's defaults. -/
structure FormLimits where
  maxFields : Nat := 1000
  maxFiles : Nat := 1000
  maxPartSize : Nat := 1024 * 1024
  deriving Inhabited, Repr

/-- What Starlette's form parsers raise (`MultiPartException`). -/
inductive LimitError where
  /-- "Too many fields. Maximum number of fields is {max_fields}." -/
  | tooManyFields (max : Nat)
  /-- "Too many files. Maximum number of files is {max_files}." -/
  | tooManyFiles (max : Nat)
  /-- "Field exceeded maximum size of {KB}KB." (urlencoded) -/
  | fieldTooLarge (max : Nat)
  /-- "Part exceeded maximum size of {KB}KB." (multipart, non-file parts) -/
  | partTooLarge (max : Nat)
  /-- "The Content-Disposition header field "name" must be provided." -/
  | missingName
  /-- "Missing boundary in multipart." -/
  | missingBoundary
  /-- "Invalid multipart data." (any parser error) -/
  | invalidMultipart
  deriving DecidableEq, Repr, Inhabited

/-- A multipart part as Starlette's `MultiPartParser` sees it: the field
name, the filename if the part is a file, the headers with lower-cased
names (Starlette's `item_headers`), and the data. Names are bytes; Starlette
decodes them with the request charset. -/
structure StarlettePart where
  name : ByteArray
  filename : Option ByteArray
  headers : List (ByteArray × ByteArray)
  data : ByteArray
  deriving Inhabited

def StarlettePart.isFile (p : StarlettePart) : Bool := p.filename.isSome

end LeanMultipart
