import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require std from git "https://github.com/leanprover/std4.git" @ leanVersion

lean_lib GameServer

@[default_target]
lean_exe gameserver {
  root := `Main
  supportInterpreter := true
}
