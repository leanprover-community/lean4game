import Lake
open Lake DSL

require GameServer from ".."/"leanserver"


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fc4a489c2af75f687338fe85c8901335360f8541"
package NNG

@[default_target]
lean_lib NNG {
  moreLeanArgs := #["-DautoImplicit=false"]
}
