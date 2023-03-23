import GameServer.Watchdog
import GameServer.FileWorker


unsafe def main : List String → IO UInt32 := fun args => do
  let e ← IO.getStderr

  Lean.enableInitializersExecution

  if args[0]? == some "--server" then
    MyServer.Watchdog.watchdogMain args
  else if args[0]? == some "--worker" then
    MyServer.FileWorker.workerMain {}
  else
    e.putStrLn s!"Expected `--server` or `--worker`"
    return 1


-- TODO: Potentially it could be useful to pass in the `gameName` via the websocket connection
