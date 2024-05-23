import GameServer.AbstractCtx

/-!
This file contains anything related to the `Hint` tactic used to add hints to a game level.
-/

open Lean Meta Elab

namespace GameServer

syntax hintArg := atomic(" (" (&"strict" <|> &"hidden" <|> &"defeq") " := " withoutPosition(term) ")")

/-- A hint to help the user with a specific goal state -/
structure GoalHintEntry where
  goal : AbstractCtxResult
  /-- Text of the hint as an expression of type `Array Expr → MessageData` -/
  text : Expr
  rawText : String
  /-- If true, then hint should be hidden and only be shown on player's request -/
  hidden : Bool := false
  /-- If true, then the goal must contain only the assumptions specified in `goal` and no others -/
  strict : Bool := false
  defeq : Bool := false

instance : Repr GoalHintEntry := {
  reprPrec := fun a n => reprPrec a.text n
}

/-- For a hint `(hint : GoalHintEntry)` one uses `(← evalHintMessage hint.text) x`
 where `(x : Array Expr)` contains the names of all the variables that should be inserted
 in the text.

 TODO: explain better. -/
unsafe def evalHintMessageUnsafe : Expr → MetaM (Array Expr → MessageData) :=
  evalExpr (Array Expr → MessageData)
    (.forallE default (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr))
      (mkConst ``MessageData) .default)

@[implemented_by evalHintMessageUnsafe]
def evalHintMessage : Expr → MetaM (Array Expr → MessageData) := fun _ => pure (fun _ => "")

/-- Remove any spaces at the beginning of a new line -/
partial def removeIndentation (s : String) : String :=
  let rec loop (i : String.Pos) (acc : String) (removeSpaces := false) : String :=
    let c := s.get i
    let i := s.next i
    if s.atEnd i then
      acc.push c
    else if removeSpaces && c == ' ' then
      loop i acc (removeSpaces := true)
    else if c == '\n' then
      loop i (acc.push c) (removeSpaces := true)
    else
      loop i (acc.push c)
  loop ⟨0⟩ ""
