import GameServer.Watchdog
import GameServer.FileWorker


def main : List String → IO UInt32 := fun args => do
  let e ← IO.getStderr
  if args[0]? == some "--server" then
    MyServer.Watchdog.watchdogMain []
  else if args[0]? == some "--worker" then
    MyServer.FileWorker.workerMain {}
  else
    e.putStrLn s!"Expected `--server` or `--worker`"
    return 1


-- TODO: Potentially it could be useful to pass in the `gameName` via the websocket connection

-- unsafe def main (args : List String) : IO UInt32 := do


--   -- Check if required arguments are given by the user
--   if args.length != 2 then
--     throw (IO.userError $ "Expected two arguments:" ++
--       "The name of the game module and the path to the game project.")
--   let gameName := args[0]!
--   let gameDir := args[1]!


--   -- Run the game
--   Server.runGame gameName
