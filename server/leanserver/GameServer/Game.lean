import Lean
import GameServer.EnvExtensions


open Lean

structure GameServerState :=
(env : Lean.Environment)
(game : Name)

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

def getGame (game : Name): GameServerM Json := do
  let some game ← getGame? game
    | throwServerError "Game not found"
  let gameJson : Json := toJson game
  -- Add world sizes to Json object
  let worldSize := game.worlds.nodes.toList.map (fun (n, w) => (n.toString, w.levels.size))
  let gameJson := gameJson.mergeObj (Json.mkObj [("worldSize", Json.mkObj worldSize)])
  return gameJson

/--
Fields:
- description: Lemma in mathematical language.
- descriptionGoal: Lemma printed as Lean-Code.
-/
structure LevelInfo where
  index : Nat
  title : String
  tactics: Array TacticAvailability
  lemmas: Array LemmaDocEntry
  introduction : String
  descrText : String := ""
  descrFormat : String := ""
deriving ToJson

structure LoadLevelParams where
  world : Name
  level : Nat
  deriving ToJson, FromJson

partial def handleServerEvent (ev : ServerEvent) : GameServerM Bool := do
  match ev with
  | ServerEvent.clientMsg msg =>
    match msg with
    | Message.request id "info" _ =>
      let s ← get
      let c ← read
      c.hOut.writeLspResponse ⟨id, (← getGame s.game)⟩
      return true
    | Message.request id "loadLevel" params =>
      let p ← parseParams LoadLevelParams (toJson params)
      let s ← get
      let c ← read
      let some lvl ← getLevel? {game := s.game, world := p.world, level := p.level}
        | do
            c.hOut.writeLspResponseError ⟨id, .invalidParams, s!"Level not found: world {p.world}, level {p.level}", none⟩
            return true
      let levelInfo : LevelInfo :=
          { index := lvl.index,
            title := lvl.title,
            tactics := lvl.tactics,
            lemmas := lvl.lemmas,
            descrText := lvl.descrText,
            descrFormat := lvl.descrFormat --toExpr <| format (lvl.goal.raw) --toString <| Syntax.formatStx (lvl.goal.raw) --Syntax.formatStx (lvl.goal.raw) , -- TODO
            introduction := lvl.introduction }
      c.hOut.writeLspResponse ⟨id, ToJson.toJson levelInfo⟩
      return true
    | _ => return false
  | _ => return false

end Game
