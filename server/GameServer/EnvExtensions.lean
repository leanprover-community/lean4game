import GameServer.HashMapExtension
import GameServer.SingleValPersistentEnvExtension

/-! # Environment extensions

The game framework stores almost all its game building data in environment extensions
defined in this file. MAyn of them are `SimplePersistentEnvExtension` but we also
use `HashMapExtension` and `SingleValPersistentEnvExtension`
-/


open Lean

/-! ## Messages -/

structure GoalMessageEntry where
  ctx_size : Nat
  normalized_goal : Expr
  intro_nb : Nat 
  message : String
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

/-! ## Game -/

structure Game where
  name : Name
  title : String := ""
  introduction : String := ""
  conclusion : String := ""
  authors : List String := []
  nb_levels : Nat := 0
  deriving Repr, Inhabited, ToJson

initialize gameExt : SingleValPersistentEnvExtension Game ← registerSingleValPersistentEnvExtension `gameExt Game

/-! ## Levels -/

/- Register a (non-persistent) environment extension to hold the current level number. -/
initialize curLevelExt : EnvExtension Nat ← registerEnvExtension (pure 0)

variable {m: Type → Type} [Monad m] [MonadEnv m]

def setCurLevelIdx (lvl : Nat) :  m Unit := 
  modifyEnv (curLevelExt.setState · lvl)

def getCurLevelIdx :  m Nat := do
  return curLevelExt.getState (← getEnv)

structure GameLevel where
  index: Nat
  title: String := default
  introduction: String := default
  conclusion: String := default
  tactics: Array TacticDocEntry := default
  lemmas: Array LemmaDocEntry := default
  messages: Array GoalMessageEntry := default
  goal : Expr := default
  intro_nb : Nat := default
  deriving Inhabited, Repr

initialize levelsExt : HashMapExtension Nat GameLevel ← mkHashMapExtension `levels Nat GameLevel

def getCurLevel [MonadError m] :  m GameLevel := do
  let idx ← getCurLevelIdx
  match (← levelsExt.find? idx) with
  | some level => return level
  | none => throwError "Couldn't find level {idx}"

