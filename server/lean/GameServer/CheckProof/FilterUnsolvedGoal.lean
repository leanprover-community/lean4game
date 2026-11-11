import Lean

open Lean Widget

namespace GameServer

/--
Removes the "unsolved goals" error of the whole proof.
`Runner` appends a `done` with an empty range at the end of the proof, so
this error is the only one with an empty range. Other "unsolved goals" errors, e.g. in an empty
`have : 0 = 1 := by` do have a range.
-/
def filterUnsolvedGoal (a : Array InteractiveDiagnostic) :
    Array InteractiveDiagnostic :=
  a.filter fun d =>
    !(d.toDiagnostic.message.startsWith "unsolved goals" && d.range.start == d.range.end)
