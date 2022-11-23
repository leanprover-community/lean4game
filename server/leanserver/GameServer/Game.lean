import Lean
import GameServer.EnvExtensions

namespace Game
open Lean
open Server
open Watchdog
open Lsp
open JsonRpc

/-- Dummy `Core.Context` value to be fed to `Lean.Core.CoreM.toIO` -/
def coreCtx : Core.Context := {
  currNamespace := Name.anonymous,
  openDecls := [],
  fileName := "<Game>",
  fileMap := { source := "", positions := #[0], lines := #[1] } }

partial def handleServerEvent (ev : ServerEvent) : ServerM Bool := do
  match ev with
  | ServerEvent.clientMsg msg =>
    match msg with
    | Message.request id "info" _ =>

      let gameDir := "testgame"

      -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
      let out ← IO.Process.output
        { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
      if out.exitCode != 0 then
        IO.eprintln out.stderr
        return true

      -- Make the paths relative to the current directory
      let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
      let currentDir ← IO.currentDir
      let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

      -- Set the search path
      Lean.searchPathRef.set paths

      let hOut := (← read).hOut
      let gameName := `TestGame
      let env ← importModules [{ module := `Init : Import }, { module := gameName : Import }] {} 0
      discard <| Core.CoreM.toIO (ctx := coreCtx) (s := { env := env }) do
        let levels := levelsExt.getState env
        let game := {← gameExt.get with nb_levels := levels.size }
        hOut.writeLspResponse ⟨id, game⟩
      return true
    | _ => return false
  | _ => return false

end Game
