import GameServer.FileWorker
import GameServer.Commands

-- TODO: The only reason we import `Commands` is so that it gets built to on `lake build`
-- should we have a different solution?

unsafe def main : List String → IO UInt32 := fun args => do
  let e ← IO.getStderr

  Lean.enableInitializersExecution

  -- TODO: remove this argument
  if args[0]? == some "--server" then
    GameServer.FileWorker.workerMain {} args
  else
    e.putStrLn s!"Expected `--server`"
    return 1
