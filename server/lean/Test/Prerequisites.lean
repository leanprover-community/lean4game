import GameApi

open Lean Elab Command GameServer

/-! The `Prerequisites` of a game: one text, formerly a list of games -/

Game "TestPrerequisites"

Prerequisites "The [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)"

#eval show CommandElabM Unit from do
  let text := (← getCurGame).tile.prerequisites
  unless text == "The [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)" do
    throwError "unexpected prerequisites: {text}"

/--
warning: Prerequisites are one text now, e.g. `Prerequisites "NNG, STG"`. The 2 strings are joined with ", ".
-/
#guard_msgs in
Prerequisites "NNG" "STG"

#eval show CommandElabM Unit from do
  let text := (← getCurGame).tile.prerequisites
  unless text == "NNG, STG" do
    throwError "unexpected prerequisites: {text}"
