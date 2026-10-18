import LeanMultipart.RepoImpl.Multipart

/-!
# Runs of part data up to the next delimiter

In part data the machine only ever holds a partial delimiter match: the
bytes after the last `CR` seen, if they begin the delimiter. Since the
delimiter `CR LF -- boundary` contains `CR` only at its first byte, after any
bytes `x` that contain no whole delimiter the machine is in
`partData (.idx (pendL d x'))`, where `x'` is the pending match before `x`
followed by `x`, and every other byte has been appended to the part data
(`Mp.fold_run`). So a run up to the next delimiter can be taken with one
copy, as upstream does with `bytes.find`, whatever the run contains: `CR`s,
`CR LF`s and near-miss delimiters cost no more than any other byte.

`runSpan` finds such a run (`findDelim` looks for the delimiter at each
occurrence of its last byte, `eqRun` compares in place); `runBulk` appends
it and computes the new match from the run's last `dlen - 1` bytes.
`Mp.runBulk_eq` proves it equal to folding `step`.
-/

namespace LeanMultipart
namespace Mp

/-- The suffix of `l` from its last `CR`, if it has one. -/
def crSuffix : Bytes → Option Bytes
  | [] => none
  | c :: l => match crSuffix l with
    | some s => some s
    | none => if c = Byte.CR then some (c :: l) else none

/-- How many trailing bytes of `l` are a partial delimiter match: the suffix
from the last `CR`, if it is a proper prefix of the delimiter `d`. -/
def pendL (d l : Bytes) : Nat :=
  match crSuffix l with
  | none => 0
  | some s => if s.length < d.length ∧ s <+: d then s.length else 0

/-- Whether `b` from `i` agrees with `d` from `j`, from offset `t` on, up to
the end of `d`. -/
def eqRun (b : ByteArray) (i : Nat) (d : ByteArray) (j t : Nat) : Bool :=
  if h : j + t < d.size then
    if h' : i + t < b.size then b[i + t] == d[j + t] && eqRun b i d j (t + 1) else false
  else true
termination_by d.size - (j + t)

/-- The first start position `p` (with its last byte at `q` or later) of the
delimiter `d` in `b` before `stop`, or `stop`: the candidates are the
occurrences of `d`'s last byte. -/
def findDelim (b d : ByteArray) (stop q : Nat) : Nat :=
  let q' := scanFor b (d[d.size - 1]?.getD 0) stop q
  if q' < stop ∧ q' < b.size then
    if eqRun b (q' + 1 - d.size) d 0 0 then q' + 1 - d.size else findDelim b d stop (q' + 1)
  else stop
termination_by stop - q
decreasing_by
  have := scanFor_ge b (d[d.size - 1]?.getD 0) stop _ q rfl
  omega

/-- A run of part data from `i`, before `stop`, that holds no whole delimiter
and is at least as long as the delimiter (0 if there is none). From a
partial match, the run must not complete it. -/
def runSpan (cx : Ctx) (s : MState) (b : ByteArray) (i stop : Nat) : Nat :=
  match s.phase with
  | .partData (.idx k) =>
    if cx.dlen ≤ k then 0 else
    let r := findDelim b cx.delim (min stop b.size) (i + cx.dlen - 1)
    if r < i + cx.dlen then 0
    else if k != 0 && eqRun b i cx.delim k 0 then 0
    else r - i
  | _ => 0

/-- Take the `n` bytes at `i` (a `runSpan`) at once: the pending match and
the run, but for the new pending match, go to the part data. -/
def runBulk (cx : Ctx) (s : MState) (b : ByteArray) (i n : Nat) : MState :=
  match s.phase with
  | .partData (.idx k) =>
    if n = 0 then s else
    let e := i + n
    let k' := pendL cx.delim.data.toList (b.extract (e - (cx.dlen - 1)) e).data.toList
    let d0 := if k = 0 then s.data else s.data ++ cx.delim.extract 0 k
    { s with phase := .partData (.idx k'), pos := s.pos + n,
             data := b.copySlice i d0 d0.size (n - k') (d0.size == 0) }
  | _ => s

end Mp
end LeanMultipart
