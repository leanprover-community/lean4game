import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require "hhu-adam" / i18n @ git leanVersion
require "leanprover-community" / batteries @ git leanVersion
require "leanprover-community" / importGraph  @ git leanVersion

@[default_target]
lean_lib GameServer

lean_lib GameServerExe

@[default_target]
lean_exe gameserver {
  root := `GameServerExe
  supportInterpreter := true
}

@[test_driver]
lean_lib TestGame

/--
When a package depending on GameServer updates its dependencies,
build the `gameserver` executable.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.name = pkg.name then
    return -- do not run in GameServer itself
  discard <| runBuild gameserver.fetch
