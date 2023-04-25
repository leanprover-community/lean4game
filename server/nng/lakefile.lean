import Lake
open Lake DSL

require GameServer from  git
  "https://github.com/leanprover-community/lean4game.git"@"main"/"server"/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fc4a489c2af75f687338fe85c8901335360f8541"

package NNG where
  moreLeanArgs := #["-DautoImplicit=false", "-Dtactic.hygienic=false"]
  moreServerArgs := #["-DautoImplicit=false", "-Dtactic.hygienic=false"]

@[default_target]
lean_lib NNG
