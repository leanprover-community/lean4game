import Lean
import GameServer.EnvExtensions


open Lean

structure GameServerState :=
(env : Lean.Environment)

abbrev GameServerM := StateT GameServerState Server.Watchdog.ServerM

instance : MonadEnv GameServerM := {
  getEnv := do return (← get).env
  modifyEnv := fun f => do
    let s ← get
    set {s with env := f s.env}
}

namespace Game
open Server
open Watchdog
open Lsp
open JsonRpc
open IO

structure LevelInfo where
  index : Nat
  title : String
  tactics: Array TacticDocEntry
  lemmas: Array LemmaDocEntry
deriving ToJson

partial def handleServerEvent (ev : ServerEvent) : GameServerM Bool := do
  match ev with
  | ServerEvent.clientMsg msg =>
    match msg with
    | Message.request id "info" _ =>
      let s ← get
      let c ← read
      let levels := levelsExt.getState s.env
      let game := {← gameExt.get with nb_levels := levels.size }
      c.hOut.writeLspResponse ⟨id, game⟩
      return true
    | Message.request id "loadLevel" _ =>
      let idx := 1
      let s ← get
      let c ← read
      let levels := levelsExt.getState s.env
      let some lvl := levels.find? idx | throwServerError s!"Cannot find level {idx}"
      let levelInfo : LevelInfo :=
          { index := lvl.index,
            title := lvl.title,
            tactics := lvl.tactics,
            lemmas := lvl.lemmas }
      c.hOut.writeLspResponse ⟨id, ToJson.toJson levelInfo⟩
      return true
    | _ => return false
  | _ => return false

end Game
