import Lake
open Lake DSL

require GameServer from ".."/"leanserver"

package NNG

@[default_target]
lean_lib NNG {
  moreLeanArgs := #["-DautoImplicit=false"]
}
