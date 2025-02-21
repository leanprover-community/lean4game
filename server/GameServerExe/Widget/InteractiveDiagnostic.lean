import Lean.Widget.InteractiveDiagnostic

namespace GameServer.Widget

open Lean.Widget (InteractiveDiagnostic)

/-- filter the "unsolved goals" message -/
def filterUnsolvedGoal (a : Array InteractiveDiagnostic) :
    Array InteractiveDiagnostic :=
  a.filter (fun d => match d.message with
  | .append ⟨(.text x) :: _⟩ => x != "unsolved goals"
  | _ => true)
