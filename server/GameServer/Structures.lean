import Lean.Widget.InteractiveGoal
import Lean.Widget.InteractiveDiagnostic
import Lean.Data.Lsp.Diagnostics

/-!
This file contains the custom data structures use by the server.

Some of them overwrite built-in structures from Lean.

In particular, the structures from `Lean.Widget.InteractiveGoal` are duplicated with
the following extension:

* `isAssumption?` in `InteractiveHypothesisBundle`: stores if a hypothesis is of type `Prop`.

NOTE: Changes here need to be reflected in  the corresponding `interface` in `rcp_api.ts`
on the client-side.
-/

open Lean Server Widget

namespace GameServer

/-- Extend the interactive hypothesis bundle with an option to distinguish
"assumptions" from "objects". "Assumptions" are hypotheses of type `Prop`. -/
-- @[inherit_doc Lean.Widget.InteractiveHypothesisBundle]
structure InteractiveHypothesisBundle extends Lean.Widget.InteractiveHypothesisBundle where
  /-- The hypothesis's type is of type `Prop` -/
  isAssumption? : Option Bool := none
deriving RpcEncodable

-- duplicated but with custom `InteractiveHypothesisBundle`
@[inherit_doc Lean.Widget.InteractiveGoalCore]
structure InteractiveGoalCore where
  hyps : Array InteractiveHypothesisBundle
  type : CodeWithInfos
  ctx : WithRpcRef Elab.ContextInfo

-- duplicated but with custom `InteractiveGoalCore`
@[inherit_doc Lean.Widget.InteractiveGoal]
structure InteractiveGoal extends InteractiveGoalCore where
  userName? : Option String
  goalPrefix : String
  mvarId : MVarId
  isInserted? : Option Bool := none
  isRemoved? : Option Bool := none
deriving RpcEncodable

-- duplicated with custom `InteractiveGoalCore`
@[inherit_doc Lean.Widget.InteractiveTermGoal]
structure InteractiveTermGoal extends InteractiveGoalCore where
  range : Lsp.Range
  term : WithRpcRef Elab.TermInfo
deriving RpcEncodable

/-- A hint in the game at the corresponding goal. -/
structure GameHint where
  text : String
  hidden : Bool
deriving FromJson, ToJson

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
  diags : Array InteractiveDiagnostic := default
  line : Option Nat -- only for debugging
  column : Option Nat -- only for debugging

deriving RpcEncodable

instance : Inhabited InteractiveGoalsWithHints := ⟨default, default, default, none, none⟩

/-- Collected goals throughout the proof. Used for communication with the game client. -/
structure ProofState where
  /-- goals after each line. includes the hints. -/
  steps : Array <| InteractiveGoalsWithHints
  /-- diagnostics contains all errors and warnings.

  TODO: I think they contain information about which line they belong to. Verify this.
  -/
  diagnostics : Array InteractiveDiagnostic := default
  /-- Whether the level is considered solved. -/
  completed : Bool
  completedWithWarnings : Bool
  lastPos : Nat -- only for debugging
deriving RpcEncodable
