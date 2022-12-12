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

def getGame (game : Name): GameServerM Game := do
  let some game ← getGame? game
    | throwServerError "Game not found"
  return game

/--

Fields:
- description: Lemma in mathematical language.
- descriptionGoal: Lemma printed as Lean-Code.
-/
structure LevelInfo where
  index : Nat
  title : String
  tactics: Array TacticDocEntry
  lemmas: Array LemmaDocEntry
  introduction : String
  description : String
  ppStatement : String
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
        | throwServerError s!"Level not found {(← getGame s.game).name} {p.world} {p.level}"
      let levelInfo : LevelInfo :=
          { index := lvl.index,
            title := lvl.title,
            tactics := lvl.tactics,
            lemmas := lvl.lemmas,
            description := lvl.description,
            ppStatement := lvl.ppStatement --toExpr <| format (lvl.goal.raw) --toString <| Syntax.formatStx (lvl.goal.raw) --Syntax.formatStx (lvl.goal.raw) , -- TODO
            introduction := lvl.introduction }
      c.hOut.writeLspResponse ⟨id, ToJson.toJson levelInfo⟩
      return true
    | _ => return false
  | _ => return false

end Game
