import GameServerExe.FileWorker
import Lake.CLI.Main

-- TODO: The only reason we import `Commands` is so that it gets built to on `lake build`
-- should we have a different solution?

open Lean System.FilePath

open Lake

unsafe def main : List String → IO UInt32 := fun args => do
  Lean.enableInitializersExecution

  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }

  Lake.serve config args.toArray

  -- let e ← IO.getStderr
  -- e.putStrLn s!"args: {args}"

  -- Lean.Server.FileWorker.workerMain {}

  -- -- TODO: remove this argument
  -- if args[0]? == some "--server" then
  --   GameServer.FileWorker.workerMain {} args
  -- else
  --   e.putStrLn s!"Expected `--server`"
  --   return 1
