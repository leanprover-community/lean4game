import Lake
open Lake DSL

package GameServer

@[default_target]
lean_lib GameServer

@[default_target]
lean_exe gameserver {
  root := `Main
  supportInterpreter := true
}
