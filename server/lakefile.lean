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

/--
When a package depending on GameServer updates its dependencies,
build the `gameserver` executable.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.name = pkg.name then
    return -- do not run in GameServer itself

  /-
  TODO: Could we use the Lake API instead of spawning a new process?
  -/
  let toolchain := ← IO.FS.readFile <| pkg.dir / "lean-toolchain"
  let exitCode ← IO.Process.spawn {
    cmd := "elan"
    args := #["run", toolchain.trim, "lake", "build", "gameserver"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    logError s!"{pkg.name}: failed to build gameserver"
