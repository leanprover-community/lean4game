import Lake
open Lake DSL

require GameServer from ".."/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

package TestGame

@[default_target]
lean_lib TestGame {
  moreLeanArgs := #["-DautoImplicit=false"]
}
