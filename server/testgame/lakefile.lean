import Lake
open Lake DSL

require GameServer from ".."/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require duper from git
  "/home/jeugster/Documents/Lean/duper"@"main"

--set_option tactic.hygienic false
--set_option autoImplicit false

package TestGame

@[default_target]
lean_lib TestGame {
  moreLeanArgs := #["-DautoImplicit=false"]
}
