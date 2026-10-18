import LeanMultipart.DataTypes.Bytes

/-!
# `OctetStreamParser`

Upstream's parser for `application/octet-stream` bodies: it reports the
data it is given, truncated at `max_size`.

```python
parser = OctetStreamParser(callbacks, max_size=float("inf"))
parser.write(chunk)   # on_start (first write), on_data
parser.finalize()     # on_end
```
-/

namespace LeanMultipart

inductive OctetEvent where
  | start
  | data (b : ByteArray)
  | «end»
  deriving Inhabited

/-- Upstream's `OctetStreamCallbacks`, in any monad. -/
structure OctetStreamCallbacks (m : Type → Type) [Monad m] where
  onStart : m Unit := pure ()
  onData : ByteArray → m Unit := fun _ => pure ()
  onEnd : m Unit := pure ()

def OctetEvent.fire {m : Type → Type} [Monad m] (cb : OctetStreamCallbacks m) : OctetEvent → m Unit
  | .start => cb.onStart
  | .data b => cb.onData b
  | .end => cb.onEnd

/-- Upstream's `OctetStreamParser` object. -/
structure OctetStreamParser where
  maxSize : Option Nat := none
  h_maxSize : ∀ m, maxSize = some m → 0 < m := by intro m h; cases h <;> decide
  size : Nat := 0
  started : Bool := false

namespace OctetStreamParser

def new (maxSize : Option Nat := none)
    (h : ∀ m, maxSize = some m → 0 < m := by intro m h; cases h <;> decide) : OctetStreamParser :=
  { maxSize, h_maxSize := h }

/-- Feed a chunk: `start` on the first write, then the data (truncated at
`maxSize`); returns the number of bytes processed. -/
def write (p : OctetStreamParser) (chunk : ByteArray) : OctetStreamParser × Array OctetEvent × Nat :=
  let n := match p.maxSize with
    | none => chunk.size
    | some m => min chunk.size (m - p.size)
  let evs : Array OctetEvent := if p.started then #[] else #[.start]
  ({ p with size := p.size + n, started := true }, evs.push (.data (chunk.extract 0 n)), n)

def finalize (_p : OctetStreamParser) : Array OctetEvent := #[.end]

def writeWith {m : Type → Type} [Monad m] (p : OctetStreamParser) (cb : OctetStreamCallbacks m)
    (chunk : ByteArray) : m (OctetStreamParser × Nat) := do
  let (p', evs, n) := p.write chunk
  for e in evs do e.fire cb
  pure (p', n)

def finalizeWith {m : Type → Type} [Monad m] (p : OctetStreamParser) (cb : OctetStreamCallbacks m) : m Unit := do
  for e in p.finalize do e.fire cb

end OctetStreamParser
end LeanMultipart
