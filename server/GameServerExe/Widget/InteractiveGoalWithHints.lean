import Lean.Widget.InteractiveDiagnostic
import GameServerExe.Widget.InteractiveGoal

namespace GameServer

open Lean Server

/-- A hint in the game at the corresponding goal. -/
structure GameHint where
  /-- The text with the variable names already inserted.

  Note: This is in theory superfluous and will be completely replaced by `rawText`. We just left
  it in for debugging for now. -/
  text : String
  /-- Flag whether the hint should be hidden initially. -/
  hidden : Bool
  /-- The text with the variables not inserted yet. -/
  rawText : String
  /-- The assignment of variable names in the `rawText` to the ones the player used. -/
  varNames : Array <| Name × Name
deriving FromJson, ToJson

namespace Widget

/-- Bundled `InteractiveGoal` together with an array of hints that apply at this stage. -/
structure InteractiveGoalWithHints where
  goal : InteractiveGoal
  /-- Extended the `InteractiveGoal` by an array of hints at that goal. -/
  hints : Array GameHint
deriving RpcEncodable

structure InteractiveGoalsWithHints where
  goals : Array InteractiveGoalWithHints
  /-- The content of the line evaluated. -/
  command : String
  diags : Array Widget.InteractiveDiagnostic := default
  line : Option Nat -- only for debugging
  column : Option Nat -- only for debugging
deriving RpcEncodable

instance : Inhabited InteractiveGoalsWithHints := ⟨default, default, default, none, none⟩

end GameServer.Widget
