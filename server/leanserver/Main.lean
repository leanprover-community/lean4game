import GameServer.Server

unsafe def main (args : List String) : IO Unit := do

  if args.length != 2 then
    throw (IO.userError "Expected two arguments: The name of the game module and the path to the game project.")

  let out ← IO.Process.output { cwd := args[1]!, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }

  if out.exitCode != 0 then
    IO.eprintln out.stderr
  else
    let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
    let currentDir ← IO.currentDir
    let paths := paths.map fun p => currentDir / (args[1]! : System.FilePath) / p
    Server.runGame (Lean.Name.mkSimple args[0]!) paths
