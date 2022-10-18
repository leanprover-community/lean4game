/-
This is the Lean 4 game server. It offers a way to interact with Lean 4 which 
is completely distinct from running the command-line lean or the language server protocol.

It is based on lean-gym by Daniel Selsam.
-/
import Lean.Data.Json.Basic

import GameServer.Utils
import GameServer.EnvExtensions

open Lean Meta Elab Tactic Std

/- Convert JSON to string without line breaks -/
-- TODO: this is too slow...
instance instToStringJsonOneLine : ToString Json := ToString.mk (fun o => (toString o).replace "\n" "")
attribute [-instance] Lean.Json.instToStringJson

/-! ## GameGoal -/
structure GameGoal where
  objects : List LocalDecl
  assumptions : List LocalDecl
  goal : String
  mvarid : MVarId

def Lean.MVarId.toGameGoal (goal : MVarId) : MetaM GameGoal := do
match (← getMCtx).findDecl? goal with
| none          => throwError "unknown goal"
| some mvarDecl => do
  -- toGameGoalAux below will sort local declarations from the context of goal into data and assumptions,
  -- discarding auxilliary declarations
  let rec toGameGoalAux : List (Option LocalDecl) → MetaM (List LocalDecl × List LocalDecl)
  | (some decl)::t => withLCtx mvarDecl.lctx mvarDecl.localInstances do
    let (o, a) ← toGameGoalAux t
    if decl.isAuxDecl then
      return (o, a)
    if (← inferType decl.type).isProp then
      return (o, decl::a)
    else
      return (decl::o, a)
  | none:: t => toGameGoalAux t
  | [] => return ([], [])
  withLCtx mvarDecl.lctx mvarDecl.localInstances do
    let (objects, assumptions) ← toGameGoalAux mvarDecl.lctx.decls.toList
    return {objects := objects, assumptions := assumptions, goal := toString (← Meta.ppExpr mvarDecl.type),
            mvarid := goal }

def GameGoal.toJson (gameGoal : GameGoal) : MetaM Json := 
gameGoal.mvarid.withContext do
  return Json.mkObj [("objects", Lean.ToJson.toJson (← gameGoal.objects.mapM Lean.LocalDecl.toJson)), 
                     ("assumptions", Lean.ToJson.toJson (← gameGoal.assumptions.mapM Lean.LocalDecl.toJson)), 
                     ("goal", gameGoal.goal)]


/-! ## Action -/

inductive Action where
| info : Action
| loadLevel : Nat → Action
| runTactic : String → Action
| undo : Action
| restartGame : Action
| restartLevel : Action
| quit : Action
| next : Action
| prev : Action
| invalid : String → Action  -- Used for broken Json parsing
deriving ToJson, FromJson, Repr

def Action.parse (s : String) : Action :=
  let e : Except String Action := 
    try
      return ← fromJson? (← Json.parse s)
    catch _ => return Action.invalid s
  match e with
  | Except.ok a => a
  | _ => Action.info

def Action.get : IO Action := 
  return Action.parse (← (← IO.getStdin).getLine)


/-! ## LevelInfo -/

structure LevelInfo extends GameLevel where
  goals    : List GameGoal := []
  errors   : Array String := #[]
  message  : String := ""

def LevelInfo.toJson (info : LevelInfo) : MetaM Json :=
  return Json.mkObj [("index", Lean.ToJson.toJson info.index),
                     ("title", Lean.ToJson.toJson info.title),
                     ("tactics", Lean.ToJson.toJson info.tactics),
                     ("lemmas", Lean.ToJson.toJson info.lemmas),
                     ("errors", Lean.ToJson.toJson info.errors),
                     ("goals", Lean.ToJson.toJson (← info.goals.mapM (·.toJson))),
                     ("message", info.message)]

namespace Server

/-! ## LevelM and Response -/

structure SavedState where
  tacticState : Tactic.SavedState
  message : String := ""

abbrev LevelM := ReaderT GameLevel StateRefT (Array SavedState) TermElabM

/-- Returns the most recent SavedState. -/
def getState : LevelM SavedState := do 
  let some state := (← get).back? | throwError "Couldn't find tactic state"
  return state


structure Response : Type where
  goals    : List GameGoal := []
  errors   : Array String := #[]
  message  : String := ""

def Response.toJson (resp : Response) : MetaM Json :=
  return Json.mkObj [("errors", Lean.ToJson.toJson resp.errors),
                     ("goals", Lean.ToJson.toJson (← resp.goals.mapM (·.toJson))),
                     ("message", resp.message)]

/-! ## Main running functions -/

/-- Dummy `Core.Context` value to be fed to `Lean.Core.CoreM.toIO` -/
def coreCtx : Core.Context := { 
  currNamespace := Name.anonymous, 
  openDecls := [],
  fileName := "<Game>",
  fileMap := { source := "", positions := #[0], lines := #[1] } }


partial def runLevel (GameName : Name) (levels : HashMap Nat GameLevel) (idx : Nat) : IO Unit := do
  let levelName : Name := s!"Level{toString idx}"
  let termElabM : TermElabM Unit := do
    let some lvl := levels.find? idx | throwError s!"Cannot find level {idx}"
    let mvar ← mkFreshExprMVar (some lvl.goal) (kind := MetavarKind.synthetic)
    let (_, mvar) ← mvar.mvarId!.introNP lvl.intro_nb
    mvar.withContext do 
      let state := #[{tacticState := { term := ← Term.saveState, tactic := { goals := [mvar] }}}]
      let levelM : LevelM Unit := do 
          let resp := {← mkResponse with message := lvl.introduction}
          let levelInfo : LevelInfo :=
              { index := lvl.index,
                title := lvl.title,
                tactics := lvl.tactics,
                lemmas := lvl.lemmas,
                errors := resp.errors,
                goals := resp.goals,
                message := resp.message }
          output (← levelInfo.toJson)
          mainLoop
      levelM.run lvl |>.run' state
  let metaM : MetaM Unit := termElabM.run' (ctx := {})
  try
    let env ← importModules [{ module := `Init : Import }, { module := GameName ++ "Levels" ++ levelName : Import }] {} 0    
    discard <| metaM.run'.toIO coreCtx { env := env }
  catch 
  | .userError s => output s!"Could not run level {idx}: {s}"
  | _ => output s!"Could not run level {idx}"
  
where

  mkResponse (errors : Array String := #[]) : LevelM Response := do
    let savedState ← getState
    let goals := savedState.tacticState.tactic.goals     
    return { goals := (← liftM $ goals.mapM Lean.MVarId.toGameGoal), message := savedState.message, errors := errors }

  /-- Try to parse the given String as a single line tactic invocation. Update the LevelM state only
  if the tactic succeeds. Always return a Response object which contains information about the current
  state with a message and errors if any. -/
  runTactic (tacticString : String) : LevelM Response := do
    let lvl ← read
    let tacticNames := (lvl.tactics.map (·.name.toString)).toList
    let tacName := (tacticString.trim.splitOn " ").headD "" 
    if not (tacticNames.contains tacName) then mkResponse #["Unrecognized tactic"] else
      let savedState ← getState
      match Parser.runParserCategory (← getEnv) `tactic tacticString "<stdin>" with
      | Except.error err => mkResponse #[err]
      | Except.ok stx    => do
        savedState.tacticState.term.restore
        let mvarId : MVarId := savedState.tacticState.tactic.goals.head!
        try
          let unsolvedGoals ← Tactic.run mvarId do set savedState.tacticState.tactic 
                                                   evalTactic stx
          if (← getThe Core.State).messages.hasErrors then
            let messages := (← getThe Core.State).messages.getErrorMessages.toList.toArray
            mkResponse (← (messages.map Message.data).mapM fun md => md.toString)
          else
            let savedState : Tactic.SavedState := { term := (← Term.saveState), tactic := { goals := unsolvedGoals}}
            let mut message := ""
            match unsolvedGoals with
            | goal::_ => do
              let normalized_tgt ← normalizedRevertExpr goal
              for msg in lvl.messages do
                if ← isDefEq normalized_tgt msg.normalized_goal then
                  message := msg.message
                  break
            | [] => pure ()
            if unsolvedGoals matches [] then
              message := (← read).conclusion
            modify fun s => s.push {tacticState := savedState, message := message}
            mkResponse
        catch ex => mkResponse #[← ex.toMessageData.toString]        

  mainLoop : LevelM Unit := do
    match ← Action.get with
    | Action.runTactic tac => do let resp ← runTactic tac; output s!"{← resp.toJson}"
    | Action.loadLevel n => runLevel GameName levels n
    | Action.undo => do modify fun s => s.pop; output s!"{← (← mkResponse).toJson}"
    | Action.restartLevel => runLevel GameName levels idx
    | Action.prev => runLevel GameName levels idx.pred
    | Action.next => runLevel GameName levels idx.succ
    | Action.quit => IO.Process.exit 0
    | Action.restartGame => output "Can't restart game now"
    | Action.info => output "Can't get info now"
    | Action.invalid s => output s!"{← { ← mkResponse with errors := #[s!"Invalid action: {s}"] : Response}.toJson}"
    mainLoop


open System Lean Std in
partial def runGame (GameName : Name) (paths : List FilePath): IO Unit := do
  searchPathRef.set paths
  let env ← importModules [{ module := `Init : Import }, { module := GameName : Import }] {} 0    
  let termElabM : TermElabM Unit := do
    let levels := levelsExt.getState env
    let game := {← gameExt.get with nb_levels := levels.size }
    mainLoop game levels
  let metaM : MetaM Unit := termElabM.run' (ctx := {})
  discard <| metaM.run'.toIO coreCtx { env := env }
where
  mainLoop (game : Game) (levels : HashMap Nat GameLevel): IO Unit := do
    match ← Action.get with
    | Action.info => output (toJson game)
    | Action.loadLevel n => runLevel GameName levels n
    | Action.quit => IO.Process.exit 0
    | Action.invalid s => output s!"Invalid action: {s}"
    | _ => output "Invalid action"
    mainLoop game levels
    
end Server
