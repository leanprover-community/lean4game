import Lake
open Lake DSL

require GameServer from ".."/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"b1cf06cb126ee163a7dc895c1aee17946ff20900"

package TestGame

@[default_target]
lean_lib TestGame
