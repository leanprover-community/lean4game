import GameServer.Message

-- TODO: Put this proxy into separate Lean project

open Lean System.FilePath IO

open Lake

/--
Game Server Proxy. Redirects messages between the client and a child process running
the Lean language server.
-/
unsafe def main : List String → IO UInt32 := fun args => do

  let gameDir :: argsᵣ := args
    | do
      IO.eprintln "ERROR: expected at least one argument"
      IO.Process.exit 1

  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr

  debug_msg s!"game directory: {gameDir}"

  try
    let leanProcess ← IO.Process.spawn {
      cwd := "../../../../../GameSkeleton"
      cmd := "lake"
      args := #["serve", "--"]
      -- env := extraEnv
      stdin := IO.Process.Stdio.piped
      stdout := IO.Process.Stdio.piped
      -- stderr := IO.Process.Stdio.piped
      }

    let i_lean : IO.FS.Stream := .ofHandle leanProcess.stdin
    let o_lean : IO.FS.Stream := .ofHandle leanProcess.stdout
    -- let e_lean : IO.FS.Stream := .ofHandle leanProcess.stderr


    let taskI ← IO.asTask do
      while true do
        /- redirect message from the client to the server -/
          let msgI : JsonRpc.Message ← GameServer.forwardMessage (← i.readLspMessage)
          i_lean.writeLspMessage msgI

    let taskO ← IO.asTask do
      while true do
          let msgO : JsonRpc.Message ← GameServer.returnMessage (← o_lean.readLspMessage)
          o.writeLspMessage msgO

          -- let msgE : JsonRpc.Message ← e_lean.readLspMessage
          -- e.writeLspMessage msgE

    match ← IO.waitAny [taskI, taskO] with
  | .ok _ =>
    IO.Process.exit 0
  | .error e =>
    IO.cancel taskI
    IO.cancel taskO
    throw e

  catch err =>
    e.putStrLn s!"GameServer error: {err}"
    IO.Process.exit 1
