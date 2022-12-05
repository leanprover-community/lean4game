import Lake
open Lake DSL

require GameServer from ".."/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"9b15aa6f091a623f992d6fff76167864794ce350"

package TestGame

@[default_target]
lean_lib TestGame
