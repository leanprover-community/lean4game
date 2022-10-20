import GameServer.Server

-- TODO: Potentially it could be useful to pass in the `gameName` via the websocket connection

unsafe def main (args : List String) : IO Unit := do

  -- Check if required arguments are given by the user
  if args.length != 2 then
    throw (IO.userError $ "Expected two arguments:" ++
      "The name of the game module and the path to the game project.")
  let gameName := args[0]!
  let gameDir := args[1]!

  -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
  let out ← IO.Process.output
    { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
  if out.exitCode != 0 then
    IO.eprintln out.stderr
    return

  -- Make the paths relative to the current directory
  let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
  let currentDir ← IO.currentDir
  let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

  -- Set the search path
  Lean.searchPathRef.set paths

  -- Run the game
  Server.runGame gameName
