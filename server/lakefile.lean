import Lake
open Lake DSL

package GameServer

require std from git "https://github.com/leanprover/std4.git"

lean_lib GameServer

@[default_target]
lean_exe gameserver {
  root := `Main
  supportInterpreter := true
}
