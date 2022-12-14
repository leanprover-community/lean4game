import Lean
/-! # Environment extensions

The game framework stores almost all its game building data in environment extensions
defined in this file.
-/


open Lean

/-! ## Messages -/

/--
A message to be displayed to the user as instruction/hint.

Fields
  (TODO)
  spoiler: If true, then message should be hidden by default
-/
structure GoalMessageEntry where
  goal : Expr
  intros : Nat
  message : String
  spoiler : Bool := false
  deriving Repr

/-! ## Tactic documentation -/

structure TacticDocEntry where
  name : Name
  content : String
  deriving ToJson, Repr

/-- Environment extension for tactic documentation. -/
initialize tacticDocExt : SimplePersistentEnvExtension TacticDocEntry (Array TacticDocEntry) ←
  registerSimplePersistentEnvExtension {
    name := `tactic_doc
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

open Elab Command in
/-- Print a registered tactic doc for debugging purposes. -/
elab "#print_tactic_doc" : command => do
  for entry in tacticDocExt.getState (← getEnv) do
    dbg_trace "{entry.name} : {entry.content}"

structure TacticSetEntry where
  name : Name
  tactics : Array TacticDocEntry
  deriving ToJson, Repr

/-- Environment extension for tactic sets. -/
initialize tacticSetExt : SimplePersistentEnvExtension TacticSetEntry (Array TacticSetEntry) ←
  registerSimplePersistentEnvExtension {
    name := `tactic_set
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

open Elab Command in
/-- Print all registered tactic sets for debugging purposes. -/
elab "#print_tactic_set" : command => do
  for entry in tacticSetExt.getState (← getEnv) do
    dbg_trace "{entry.name} : {entry.tactics.map TacticDocEntry.name}"

/-! ## Lemma documentation -/

structure LemmaDocEntry where
  name : Name
  userName : Name
  category : String
  content : String
  deriving ToJson, Repr

/-- Environment extension for lemma documentation. -/
initialize lemmaDocExt : SimplePersistentEnvExtension LemmaDocEntry (Array LemmaDocEntry) ←
  registerSimplePersistentEnvExtension {
    name := `lemma_doc
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

open Elab Command in
/-- Print a lemma doc for debugging purposes. -/
elab "#print_lemma_doc" : command => do
  for entry in lemmaDocExt.getState (← getEnv) do
    dbg_trace "{entry.userName} ({entry.name}) in {entry.category}: {entry.content}"

structure LemmaSetEntry where
  name : Name
  title : String
  lemmas : Array LemmaDocEntry
  deriving ToJson, Repr

/-- Environment extension for lemma sets. -/
initialize lemmaSetExt : SimplePersistentEnvExtension LemmaSetEntry (Array LemmaSetEntry) ←
  registerSimplePersistentEnvExtension {
    name := `lemma_set
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

open Elab Command in
/-- Print all registered lemma sets for debugging purposes. -/
elab "#print_lemma_set" : command => do
  for entry in lemmaSetExt.getState (← getEnv) do
    dbg_trace "{entry.name} : {entry.lemmas.map LemmaDocEntry.name}"

/-! ## Graph -/

structure Graph (α β : Type) [inst : BEq α] [inst : Hashable α] where
  nodes: HashMap α β := {}
  edges: Array (α × α) := {}
deriving Inhabited

instance [inst : BEq α] [inst : Hashable α] [ToJson α] : ToJson (Graph α β) := {
  toJson := fun graph => Json.mkObj [
    ("nodes", toJson (graph.nodes.toArray.map Prod.fst)),
    ("edges", toJson graph.edges)
  ]
}

instance [inst : BEq α] [inst : Hashable α] : EmptyCollection (Graph α β) := ⟨default⟩

def Graph.insertNode [inst : BEq α] [inst : Hashable α] (g : Graph α β) (a : α) (b : β) :=
  {g with nodes := g.nodes.insert a b}

/-! ## Environment extensions for game specification-/

/-- Register a (non-persistent) environment extension to hold the current level -/
initialize curGameExt : EnvExtension (Option Name) ← registerEnvExtension (pure none)
/-- Register a (non-persistent) environment extension to hold the current level -/
initialize curWorldExt : EnvExtension (Option Name) ← registerEnvExtension (pure none)
/-- Register a (non-persistent) environment extension to hold the current level -/
initialize curLevelExt : EnvExtension (Option Nat) ← registerEnvExtension (pure none)

inductive Layer :=
| Game | World | Level

variable {m: Type → Type} [Monad m] [MonadEnv m]

def setCurGameId (game : Name) : m Unit :=
  modifyEnv (curGameExt.setState · (some game))

def setCurWorldId (world : Name) : m Unit :=
  modifyEnv (curWorldExt.setState · (some world))

def setCurLevelIdx (level : Nat) : m Unit :=
  modifyEnv (curLevelExt.setState · (some level))

def getCurLayer [MonadError m] : m Layer := do
  match curGameExt.getState (← getEnv), curWorldExt.getState (← getEnv), curLevelExt.getState (← getEnv) with
  | some _, some _, some _ => return Layer.Level
  | some _, some _, none => return Layer.World
  | some _, none, none => return Layer.Game
  | _, _, _ => throwError "Invalid Layer"

def getCurGameId [MonadError m] : m Name := do
  match curGameExt.getState (← getEnv) with
  | some game => return game
  | none => throwError "Current game not set"

def getCurWorldId [MonadError m] : m Name := do
  match curWorldExt.getState (← getEnv) with
  | some world => return world
  | none => throwError "Current world not set"

def getCurLevelIdx [MonadError m] : m Nat := do
  match curLevelExt.getState (← getEnv) with
  | some level => return level
  | none => throwError "Current level not set"

/-! ## Levels -/

structure LevelId where
  game : Name
  world : Name
  level : Nat
deriving Inhabited

def getCurLevelId [MonadError m] : m LevelId := do
  return { game := ← getCurGameId, world := ← getCurWorldId, level := ← getCurLevelIdx}

/--


Fields:
- TODO
- introduction: Theory block shown all the time.
- description:  The mathematical statemtent in mathematician-readable form.
- goal:         The statement in Lean.
- conclusion:   Displayed when level is completed.
-/
structure GameLevel where
  index: Nat
  title: String := default
  introduction: String := default
  description: String := default
  conclusion: String := default
  tactics: Array TacticDocEntry := default
  lemmas: Array LemmaDocEntry := default
  messages: Array GoalMessageEntry := default
  goal : TSyntax `Lean.Parser.Command.declSig := default
  descrText: String := default
  descrFormat : String := default
  deriving Inhabited, Repr

/-! ## World -/

structure World where
  name: Name
  title: String := ""
  introduction: String := ""
  conclusion : String := ""
  levels: HashMap Nat GameLevel := {}
deriving Inhabited

/-! ## Game -/

structure Game where
  name : Name
  title : String := ""
  introduction : String := ""
  conclusion : String := ""
  authors : List String := []
  worlds : Graph Name World := {}
deriving Inhabited, ToJson

/-! ## Game environment extension -/

def HashMap.merge [BEq α] [Hashable α] (old : HashMap α β) (new : HashMap α β) (merge : β → β → β) :
  HashMap α β :=
new.fold (fun acc a b =>
  if let some bOld := acc.find? a
  then acc.insert a (merge bOld b)
  else acc.insert a b) old

def GameLevel.merge (old : GameLevel) (new : GameLevel) : GameLevel :=
  new -- simply override old level

def World.merge (old : World) (new : World) : World :=
{ new with
  levels := HashMap.merge old.levels new.levels GameLevel.merge}

def Game.merge (old : Game) (new : Game) : Game :=
{ new with
  worlds := {
    nodes := HashMap.merge old.worlds.nodes new.worlds.nodes World.merge
    edges := Id.run do
      let mut res := old.worlds.edges
      for e in new.worlds.edges do
        if ¬ res.contains e then
          res := res.push e
      return res
  } }

initialize gameExt : PersistentEnvExtension (Name × Game) (Name × Game) (HashMap Name Game) ←
  do registerPersistentEnvExtension {
    name          := `gameExt,
    mkInitial     := pure {},
    addImportedFn := fun ess => do
      let mut games := {}
      for es in ess do
        for (name, game) in es do
          match games.find? name with
          | some oldgame =>
            games := games.insert name (Game.merge oldgame game)
          | none =>
            games := games.insert name game
      return games
    addEntryFn    := (λ s n => s.insert n.1 n.2),
    exportEntriesFn := HashMap.toArray,
    statsFn := fun s => format "number of local entries: " ++ format s.size
}

def getGame? (n : Name) : m (Option Game) := do
  return (gameExt.getState (← getEnv)).find? n

def insertGame (n : Name) (g : Game) : m Unit := do
  modifyEnv (gameExt.addEntry · (n, g))

def getLevel? (levelId : LevelId) : m (Option GameLevel) := do
  let some game ← getGame? levelId.game
    | return none
  let some world := game.worlds.nodes.find? levelId.world
    | return none
  let some level := world.levels.find? levelId.level
    | return none
  return level

def getCurGame [MonadError m] : m Game := do
  let some game ← getGame? (← getCurGameId)
    | throwError m!"Game {← getCurGameId} does not exist"
  return game

def modifyCurGame (fn : Game → m Game) [MonadError m] : m Unit := do
  let game ← getCurGame
  insertGame game.name (← fn game)

def addWorld (world : World) [MonadError m] : m Unit := do
  modifyCurGame fun game => do
    return {game with worlds := game.worlds.insertNode world.name world}

def getCurWorld [MonadError m] : m World := do
  let some world := (← getCurGame).worlds.nodes.find? (← getCurWorldId)
    | throwError m!"World {← getCurWorldId} does not exist"
  return world

def modifyCurWorld (fn : World → m World) [MonadError m] : m Unit := do
  modifyCurGame fun game => do
    let world ← getCurWorld
    return {game with worlds := {game.worlds with nodes := game.worlds.nodes.insert world.name (← fn world) }}

def addLevel (level : GameLevel) [MonadError m] : m Unit := do
  modifyCurWorld fun world => do
    return {world with levels := world.levels.insert level.index level}

def getCurLevel [MonadError m] : m GameLevel := do
  let some level := (← getCurWorld).levels.find? (← getCurLevelIdx)
    | throwError m!"Level {← getCurLevelIdx} does not exist"
  return level

def modifyCurLevel (fn : GameLevel → m GameLevel) [MonadError m] : m Unit := do
  modifyCurWorld fun world => do
    let level ← getCurLevel
    return {world with levels := world.levels.insert level.index (← fn level)}
