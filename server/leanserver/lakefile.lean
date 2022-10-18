import Lake
open Lake DSL

package GameServer

lean_lib GameServer

@[defaultTarget]
lean_exe gameserver {
  root := `Main
  supportInterpreter := true
}
