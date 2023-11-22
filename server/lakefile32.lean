import Lake
open Lake DSL

package GameServer {
  buildDir := ".lake/build32"
}

@[default_target]
lean_lib GameServer

@[default_target]
lean_exe gameserver {
  root := `Main
  supportInterpreter := true
}
