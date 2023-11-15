import GameServer.FileWorker
import GameServer.Watchdog
import GameServer.WasmServer
import GameServer.Commands

-- TODO: The only reason we import `Commands` is so that it gets built to on `lake build`
-- should we have a different solution?

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
