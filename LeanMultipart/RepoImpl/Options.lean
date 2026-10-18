import LeanMultipart.DataTypes.Boundary

/-!
# `parse_options_header`

Upstream's `parse_options_header`, which splits a `Content-Type` or
`Content-Disposition` value into the main value and its parameters, on
bytes (upstream decodes as Latin-1, so a byte is a character).

Splitting follows upstream's vendored `email.message._parseparam`: the value
is cut at `;`, except that a piece whose count of `"` minus count of `\"` is
odd so far is joined with the next piece (a `;` inside a quoted string does
not split). Each piece is stripped; before an `=` the key is right-stripped
and lower-cased, after it the value is left-stripped.

Then, per parameter: a key containing `*` (RFC 2231/5987 extended syntax,
`filename*=`) is ignored, as RFC 7578 §4.2 requires and upstream does
(`test_ignores_rfc_2231_extended_param`); a value in double quotes is
unquoted (`\\` to `\`, then `\"` to `"`); a `filename` that looks like a
Windows path keeps only its last component (the IE6 workaround). A repeated
key keeps its first position and its last value, as a Python `dict` does.
-/

namespace LeanMultipart
namespace Options

/-- A parameter value the quoted-string printer writes unescaped: no `"`,
`\` or `;`. -/
def SafeParam (l : Bytes) : Prop := ∀ c ∈ l, c ≠ Byte.DQUOTE ∧ c ≠ Byte.BSLASH ∧ c ≠ Byte.SEMI

instance (l : Bytes) : Decidable (SafeParam l) := by unfold SafeParam; exact inferInstance

/-- Strip Python whitespace from both ends. -/
def strip (l : Bytes) : Bytes := ((l.dropWhile Byte.isPySpace).reverse.dropWhile Byte.isPySpace).reverse
def lstrip (l : Bytes) : Bytes := l.dropWhile Byte.isPySpace
def rstrip (l : Bytes) : Bytes := (l.reverse.dropWhile Byte.isPySpace).reverse

/-- Split at every `;`, accumulating the current piece reversed. -/
def splitSemiGo : Bytes → Bytes → List Bytes
  | acc, [] => [acc.reverse]
  | acc, c :: cs => if c == Byte.SEMI then acc.reverse :: splitSemiGo [] cs else splitSemiGo (c :: acc) cs

/-- Split at every `;`. -/
def splitSemi (l : Bytes) : List Bytes := splitSemiGo [] l

/-- `count('"') - count('\\"')`, as an integer. -/
def quoteDiff : Bytes → Int
  | [] => 0
  | c :: d :: rest =>
    if c == Byte.BSLASH && d == Byte.DQUOTE then quoteDiff rest
    else if c == Byte.DQUOTE then 1 + quoteDiff (d :: rest)
    else quoteDiff (d :: rest)
  | [c] => if c == Byte.DQUOTE then 1 else 0

/-- Join pieces while the running quote count is odd. -/
def group : List Bytes → List Bytes
  | [] => []
  | p :: ps => groupAux p (quoteDiff p) ps
where
  groupAux (acc : Bytes) (d : Int) : List Bytes → List Bytes
    | [] => [acc]
    | q :: qs =>
      if d % 2 == 0 then acc :: groupAux q (quoteDiff q) qs
      else groupAux (acc ++ [Byte.SEMI] ++ q) (d + quoteDiff q) qs

/-- One `_parseparam` piece: `key=value` normalised, then stripped. -/
def normPiece (f : Bytes) : Bytes :=
  match f.idxOf? Byte.EQ with
  | none => strip f
  | some i => strip ((rstrip (f.take i)).map Byte.pyLower ++ [Byte.EQ] ++ lstrip (f.drop (i + 1)))

/-- `_parseparam`: the pieces of a header value. -/
def parseParam (l : Bytes) : List Bytes := (group (splitSemi l)).map normPiece

/-- Replace every non-overlapping occurrence of `old` (two bytes) by `new`,
left to right, as `bytes.replace`. -/
def replace2 (a b : UInt8) (new : UInt8) : Bytes → Bytes
  | [] => []
  | [c] => [c]
  | c :: d :: rest =>
    if c == a && d == b then new :: replace2 a b new rest
    else c :: replace2 a b new (d :: rest)

/-- Remove surrounding double quotes and undo `\\` and `\"`. -/
def unquote (v : Bytes) : Bytes :=
  if 2 ≤ v.length && v.head? == some Byte.DQUOTE && v.getLast? == some Byte.DQUOTE then
    replace2 Byte.BSLASH Byte.DQUOTE Byte.DQUOTE
      (replace2 Byte.BSLASH Byte.BSLASH Byte.BSLASH ((v.drop 1).dropLast))
  else v

/-- The IE6 workaround: a filename like `C:\path\file` or `\\host\file`
keeps its last component. -/
def ie6 (v : Bytes) : Bytes :=
  if (v.drop 1).take 2 == [Byte.COLON, Byte.BSLASH] || v.take 2 == [Byte.BSLASH, Byte.BSLASH] then
    ((v.splitOn Byte.BSLASH).getLast?).getD []
  else v

/-- Insert into an association list with Python `dict` semantics. -/
def dictSet (k v : Bytes) : List (Bytes × Bytes) → List (Bytes × Bytes)
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: dictSet k v rest

/-- `partition("=")`. -/
def partitionEq (s : Bytes) : Bytes × Bytes :=
  match s.idxOf? Byte.EQ with
  | none => (s, [])
  | some i => (s.take i, s.drop (i + 1))

/-- Fold the parameter pieces into the options dictionary. -/
def addParams : List (Bytes × Bytes) → List Bytes → List (Bytes × Bytes)
  | d, [] => d
  | d, seg :: segs =>
    let (key, val) := partitionEq seg
    if key.contains 42 then addParams d segs
    else
      let val := unquote val
      let val := if key == ascii "filename" then ie6 val else val
      addParams (dictSet key val d) segs

/-- Upstream's `parse_options_header`: the main value and the parameters,
in first-seen order. -/
def parseL (l : Bytes) : Bytes × List (Bytes × Bytes) :=
  if l.isEmpty then ([], [])
  else if !(l.contains Byte.SEMI) then (strip (l.map Byte.pyLower), [])
  else
    match parseParam l with
    | [] => ([], [])
    | ctype :: segs => (ctype, addParams [] segs)

/-- Look a parameter up. -/
def lookup (opts : List (Bytes × Bytes)) (k : Bytes) : Option Bytes :=
  (opts.find? (fun p => p.1 == k)).map (·.2)

end Options

/-- `parse_options_header` on byte arrays. -/
def parseOptionsHeader (b : ByteArray) : ByteArray × List (ByteArray × ByteArray) :=
  let (v, opts) := Options.parseL b.data.toList
  (⟨v.toArray⟩, opts.map (fun p => (⟨p.1.toArray⟩, ⟨p.2.toArray⟩)))

end LeanMultipart
