import LeanMultipart.DataTypes.Bytes

/-!
# Querystring parser types

The state of the byte-at-a-time `application/x-www-form-urlencoded` state
machine (upstream's `QuerystringParser`), its configuration, errors and
callback events.
-/

namespace LeanMultipart

/-- Upstream's `QuerystringParser` options. -/
structure QsConfig where
  strict : Bool := false
  maxSize : Option Nat := none
  deriving Inhabited, Repr

inductive QsErrorKind where
  /-- "Skipping duplicate ampersand" (strict mode) -/
  | duplicateAmpersand
  /-- "When strict_parsing is True, we require an equals sign in all field
  chunks" -/
  | missingEquals
  deriving DecidableEq, Repr, Inhabited

structure QsError where
  kind : QsErrorKind
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Upstream's `QuerystringState`, plus the terminal failure. `beforeField`
carries upstream's `_found_sep` flag. -/
inductive QsPhase where
  | beforeField (foundSep : Bool)
  | fieldName
  | fieldData
  | failed (e : QsError)
  deriving DecidableEq, Repr, Inhabited

/-- One raw field: name and value bytes as they appear in the body, still
percent-encoded. A field with no `=`, or with nothing after it, has an empty
value. -/
abbrev QsField := ByteArray × ByteArray

structure QsState where
  phase : QsPhase := .beforeField false
  pos : Nat := 0
  nameStart : Nat := 0
  name : Array UInt8 := #[]
  value : Array UInt8 := #[]
  fields : Array QsField := #[]
  deriving Inhabited

/-- The callbacks of upstream's `QuerystringParser`, as data. -/
inductive QsEvent where
  | fieldStart
  | fieldName (b : ByteArray)
  | fieldData (b : ByteArray)
  | fieldEnd
  | «end»
  deriving Inhabited

end LeanMultipart
