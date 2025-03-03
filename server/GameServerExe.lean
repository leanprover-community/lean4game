import GameServerExe.Rpc
import GameServerExe.Message
import Lake.CLI.Main

-- TODO: The only reason we import `Commands` is so that it gets built to on `lake build`
-- should we have a different solution?

open Lean System.FilePath IO

open Lake

/--
Game Server Proxy. Redirects messages between the client and a child process running
the Lean language server.

Note: we use the code from `Lake.serve` to create a child process `leanProcess`
-/
unsafe def main : List String → IO UInt32 := fun args => do
  Lean.enableInitializersExecution

  let gameDir :: argsᵣ := args
    | do
      IO.eprintln "ERROR: expected at least one argument"
      IO.Process.exit 1

  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr

  debug_msg s!"game directory: {gameDir}"

  try
    let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
    let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }

    -- copied from: `Lake.serve config args.toArray`
    let (extraEnv, moreServerArgs) ← do
      let (ws?, log) ← (loadWorkspace config).captureLog
      log.replay (logger := MonadLog.stderr)
      if let some ws := ws? then
        let ctx := mkLakeContext ws
        pure (← LakeT.run ctx getAugmentedEnv, ws.root.moreGlobalServerArgs)
      else
        IO.eprintln "warning: package configuration has errors, falling back to plain `lean --server`"
        pure (config.lakeEnv.baseVars.push (invalidConfigEnvVar, log.toString), #[])
    let leanProcess ← IO.Process.spawn {
      cmd := config.lakeEnv.lean.lean.toString
      args := #["--server"] ++ moreServerArgs ++ argsᵣ
      env := extraEnv
      stdin := IO.Process.Stdio.piped
      stdout := IO.Process.Stdio.piped
      -- stderr := IO.Process.Stdio.piped
      }

    let i_lean : IO.FS.Stream := .ofHandle leanProcess.stdin
    let o_lean : IO.FS.Stream := .ofHandle leanProcess.stdout
    -- let e_lean : IO.FS.Stream := .ofHandle leanProcess.stderr

    while true do
      /- redirect message from the client to the server -/

      let msgI : JsonRpc.Message := GameServer.forwardMessage (← i.readLspMessage)
      i_lean.writeLspMessage msgI

      let msgO : JsonRpc.Message := GameServer.returnMessage (← o_lean.readLspMessage)
      o.writeLspMessage msgO

      -- let msgE : JsonRpc.Message ← e_lean.readLspMessage
      -- e.writeLspMessage msgE

    IO.Process.exit 0
  catch err =>
    e.putStrLn s!"GameServer error: {err}"
    IO.Process.exit 1
