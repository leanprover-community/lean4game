import GameServer.RpcHandlers

open Lean

structure GameServerState :=
(env : Lean.Environment)
(game : Name)
(gameDir : String)

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
  tactics : Array InventoryTile
  lemmas : Array InventoryTile
  definitions : Array InventoryTile
  introduction : String
  conclusion : String
  descrText : Option String := none
  descrFormat : String := ""
  lemmaTab : Option String
  statementName : Option String
deriving ToJson, FromJson

structure LoadLevelParams where
  world : Name
  level : Nat
  deriving ToJson, FromJson

structure DidOpenLevelParams where
  uri : String
  gameDir : String
  levelModule : Name
  tactics : Array InventoryTile
  lemmas : Array InventoryTile
  definitions : Array InventoryTile
  deriving ToJson, FromJson

structure LoadDocParams where
  name : Name
  type : InventoryType
deriving ToJson, FromJson

def handleDidOpenLevel (params : Json) : GameServerM Unit := do
  let p ← parseParams _ params
  let m := p.textDocument
  -- Execute the regular handling of the `didOpen` event
  handleDidOpen p
  let fw ← findFileWorker! m.uri
  -- let s ← get
  let c ← read
  let some lvl ← GameServer.getLevelByFileName? c.initParams ((System.Uri.fileUriToPath? m.uri).getD m.uri |>.toString)
    | do
      c.hLog.putStr s!"Level not found: {m.uri} {c.initParams.rootUri?}"
      c.hLog.flush
  -- Send an extra notification to the file worker to inform it about the level data
  fw.stdin.writeLspNotification {
    method := "$/game/didOpenLevel"
    param  := {
      uri := m.uri
      gameDir := (← get).gameDir
      levelModule := lvl.module
      tactics := lvl.tactics.tiles
      lemmas := lvl.lemmas.tiles
      definitions := lvl.definitions.tiles
      : DidOpenLevelParams
    }
  }


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

      let env ← getEnv

      let levelInfo : LevelInfo :=
          { index := lvl.index,
            title := lvl.title,
            tactics := lvl.tactics.tiles,
            lemmas := lvl.lemmas.tiles,
            definitions := lvl.definitions.tiles,
            descrText := lvl.descrText,
            descrFormat := lvl.descrFormat --toExpr <| format (lvl.goal.raw) --toString <| Syntax.formatStx (lvl.goal.raw) --Syntax.formatStx (lvl.goal.raw) , -- TODO
            introduction := lvl.introduction
            conclusion := lvl.conclusion
            lemmaTab := lvl.lemmaTab
            statementName := match lvl.statementName with
              | .anonymous => none
              | name => match (inventoryExt.getState env).find?
                  (fun x => x.name == name && x.type == .Lemma) with
                | some n => n.displayName
                | none => name.toString
                -- Note: we could call `.find!` because we check in `Statement` that the
                -- lemma doc must exist.
            }
      c.hOut.writeLspResponse ⟨id, ToJson.toJson levelInfo⟩
      return true
    | Message.request id "loadDoc" params =>
      let p ← parseParams LoadDocParams (toJson params)
      -- let s ← get
      let c ← read
      let some doc ← getInventoryItem? p.name p.type
        | do
            c.hOut.writeLspResponseError ⟨id, .invalidParams,
              s!"Documentation not found: {p.name}", none⟩
            return true
      -- TODO: not necessary at all?
      -- Here we only need to convert the fields that were not `String` in the `InventoryDocEntry`
      -- let doc : InventoryItem := { doc with
      --   name := doc.name.toString }
      c.hOut.writeLspResponse ⟨id, ToJson.toJson doc⟩
      return true
    | _ => return false
  | _ => return false

end Game
