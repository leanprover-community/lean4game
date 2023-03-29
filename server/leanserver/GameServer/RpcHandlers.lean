import Lean
import GameServer.EnvExtensions
import GameServer.InteractiveGoal

open Lean
open Server
open Widget
open RequestM
open Meta


/-! ## GameGoal -/

namespace GameServer

def splitRootUri (initParams : Lsp.InitializeParams) (i : Nat): Option String := Id.run do
  let some rootUri := initParams.rootUri?
    | return none
  let rootUriParts := rootUri.splitOn "/"
  if rootUriParts.length == 3 then
    return rootUriParts[i]?
  return none

def levelIdFromFileName? (initParams : Lsp.InitializeParams) (fileName : String) : Option LevelId := Id.run do
  let fileParts := fileName.splitOn "/"
  if fileParts.length == 3 then
    if let (some level, some game) := (fileParts[2]!.toNat?, splitRootUri initParams 2) then
      return some {game, world := fileParts[1]!, level := level}
  return none

def gameDirFromInitParams (initParams : Lsp.InitializeParams) : Option String :=
  (splitRootUri initParams 0).map (s!"../../../{·}")

def getLevelByFileName? [Monad m] [MonadEnv m] (initParams : Lsp.InitializeParams) (fileName : String) : m (Option GameLevel) := do
  let some levelId := levelIdFromFileName? initParams fileName
    | return none
  return ← getLevel? levelId

structure FVarBijection :=
  (forward : HashMap FVarId FVarId)
  (backward : HashMap FVarId FVarId)

instance : EmptyCollection FVarBijection := ⟨{},{}⟩

def FVarBijection.insert (bij : FVarBijection) (a b : FVarId) : FVarBijection :=
  ⟨bij.forward.insert a b, bij.backward.insert b a⟩

def FVarBijection.insert? (bij : FVarBijection) (a b : FVarId) : Option FVarBijection :=
  let a' := bij.forward.find? a
  let b' := bij.forward.find? b
  if (a' == none || a' == some b) && (b' == none || b' == some a)
  then some $ bij.insert a b
  else none

/-- Checks if `pattern` and `e` are equal up to FVar identities. -/
partial def matchExpr (pattern : Expr) (e : Expr) (bij : FVarBijection := {}) : Option FVarBijection :=
  match pattern, e with
  | .bvar i1, .bvar i2 => if i1 == i2 then bij else none
  | .fvar i1, .fvar i2 => bij.insert? i1 i2
  | .mvar _, .mvar _ => bij
  | .sort u1, .sort u2 => bij -- TODO?
  | .const n1 ls1, .const n2 ls2 =>
    if n1 == n2 then bij else none -- && (← (ls1.zip ls2).allM fun (l1, l2) => Meta.isLevelDefEq l1 l2)
  | .app f1 a1, .app f2 a2 =>
    some bij
      |> (Option.bind · (fun bij => matchExpr f1 f2 bij))
      |> (Option.bind · (fun bij => matchExpr a1 a2 bij))
  | .lam _ t1 b1 _, .lam _ t2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr v1 v2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .lit l1, .lit l2 =>
    if l1 == l2 then bij else none
  | .proj i1 n1 e1, .proj i2 n2 e2 =>
    if i1 == i2 && n1 == n2 then matchExpr e1 e2 bij else none
  -- ignore mdata:
  | .mdata _ pattern', _ =>
    matchExpr pattern' e bij
  | _, .mdata _ e' =>
    matchExpr pattern e' bij
  | _, _ => none

/-- Check if each fvar in `patterns` has a matching fvar in `fvars` -/
def matchDecls (patterns : Array Expr) (fvars : Array Expr) (strict := true) (initBij : FVarBijection := {}) : MetaM Bool := do
  -- We iterate through the array backwards hoping that this will find us faster results
  -- TODO: implement backtracking
  let mut bij := initBij
  for i in [:patterns.size] do
    let pattern := patterns[patterns.size - i - 1]!
    if bij.forward.contains pattern.fvarId! then
      continue
    for j in [:fvars.size] do
      let fvar := fvars[fvars.size - j - 1]!
      if bij.backward.contains fvar.fvarId! then
        continue

      if let some bij' := matchExpr
          (← instantiateMVars $ ← inferType pattern)
          (← instantiateMVars $ ← inferType fvar) bij then
        -- usedFvars := usedFvars.set! (fvars.size - j - 1) true
        bij := bij'.insert pattern.fvarId! fvar.fvarId!
        break
    if ! bij.forward.contains pattern.fvarId! then return false

  if strict then
    return fvars.all (fun fvar => bij.backward.contains fvar.fvarId!)
  return true

unsafe def evalHintMessageUnsafe : Expr → MetaM (Array Expr → MessageData) :=
  evalExpr (Array Expr → MessageData)
    (.forallE default (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr))
      (mkConst ``MessageData) .default)

@[implemented_by evalHintMessageUnsafe]
def evalHintMessage : Expr → MetaM (Array Expr → MessageData) := fun _ => pure (fun _ => "")

open Meta in
/-- Find all hints whose trigger matches the current goal -/
def findHints (goal : MVarId) (doc : FileWorker.EditableDocument) (initParams : Lsp.InitializeParams) : MetaM (Array GameHint) := do
  goal.withContext do
    let some level ← getLevelByFileName? initParams doc.meta.mkInputContext.fileName
      | throwError "Level not found: {doc.meta.mkInputContext.fileName}"
    let hints ← level.hints.filterMapM fun hint => do
      openAbstractCtxResult hint.goal fun hintFVars hintGoal => do
        if let some fvarBij := matchExpr (← instantiateMVars $ hintGoal) (← instantiateMVars $ ← inferType $ mkMVar goal)
        then
          let lctx := (← goal.getDecl).lctx
          if ← matchDecls hintFVars lctx.getFVars (strict := hint.strict) (initBij := fvarBij)
          then
            let text := (← evalHintMessage hint.text) hintFVars
            let ctx := {env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := {}}
            let text ← (MessageData.withContext ctx text).toString
            return some { text := text, hidden := hint.hidden }
          else return none
        else
          return none
    return hints

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option InteractiveGoals)) := do
  let doc ← readDoc
  let rc ← readThe RequestContext
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- TODO: I couldn't find a good condition to find the correct snap. So we are looking
  -- for the first snap with goals here:
  withWaitFindSnap doc (fun s => ¬ (s.infoTree.goalsAt? doc.meta.text hoverPos).isEmpty)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals : List InteractiveGoals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ciAfter := { ci with mctx := ti.mctxAfter }
          let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
          -- compute the interactive goals
          let goals ← ci.runMetaM {} do
            return List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
          let goals ← ci.runMetaM {} do
             goals.mapM fun goal => do
              let hints ← findHints goal doc rc.initParams
              return ← goalToInteractive goal hints
          -- compute the goal diff
          -- let goals ← ciAfter.runMetaM {} (do
          --     try
          --       Widget.diffInteractiveGoals useAfter ti goals
          --     catch _ =>
          --       -- fail silently, since this is just a bonus feature
          --       return goals
          -- )
          return {goals}
        return some <| goals.foldl (· ++ ·) ⟨#[]⟩
      else
        return none

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    getInteractiveGoals

end GameServer
