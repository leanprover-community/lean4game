/- This file is adapted from `Lean/Server/FileWorker.lean`. -/
import Lean.Server.FileWorker
import GameServer.Game
import GameServer.ImportModules
import GameServer.SaveData
import GameServer.EnvExtensions
import GameServer.Tactic.LetIntros
import GameServer.Helpers.Tmp

namespace MyModule

open Lean
open Elab
open Parser

private def mkErrorMessage (c : InputContext) (pos : String.Pos) (errorMsg : String) : Message :=
  let pos := c.fileMap.toPosition pos
  { fileName := c.fileName, pos := pos, data := errorMsg }

private def mkEOI (pos : String.Pos) : Syntax :=
  let atom := mkAtom (SourceInfo.original "".toSubstring pos "".toSubstring pos) ""
  mkNode ``Command.eoi #[atom]

partial def parseTactic (inputCtx : InputContext) (pmctx : ParserModuleContext)
  (mps : ModuleParserState) (messages : MessageLog) :
    Syntax × ModuleParserState × MessageLog × String.Pos := Id.run do
  let mut pos := mps.pos
  let mut recovering := mps.recovering
  let mut messages := messages
  let mut stx := Syntax.missing  -- will always be assigned below

  let tokens := getTokenTable pmctx.env

  let s   := whitespace.run inputCtx pmctx tokens { cache := initCacheForInput inputCtx.input, pos }
  let endOfWhitespace := s.pos

  let p   :=  (Tactic.sepByIndentSemicolon tacticParser).fn
  let s   := p.run inputCtx pmctx tokens { cache := initCacheForInput inputCtx.input, pos }

  match s.errorMsg with
  | none =>
    stx := s.stxStack.back
    recovering := false
  | some errorMsg =>
    messages := messages.add <|  mkErrorMessage inputCtx s.pos (toString errorMsg)
    recovering := true
    stx := s.stxStack.back
    if ¬ inputCtx.input.atEnd s.pos then
      messages := messages.add <|  mkErrorMessage inputCtx s.pos "end of input"
  return (stx, { pos := inputCtx.input.endPos, recovering }, messages, endOfWhitespace)

end MyModule

namespace GameServer.FileWorker

open Lean
open Lean.Server
open Lean.Server.FileWorker
open Lsp
open IO
open Snapshots
open JsonRpc

/--
Game-specific state to be packed on top of the `Server.FileWorker.WorkerState`
used by the Lean server.
-/
structure WorkerState where
  /--
  Collection of items which are considered unlocked.
  Tactics and theorems are mixed together.
  -/
  inventory : Array String
  /--
  Difficulty determines whether tactics/theorems can be locked.
  * 0: do not check
  * 1: give warnings when locked items are used
  * 2: give errors when locked items are used
  -/
  difficulty : Nat
  /--
  `levelInfo` contains all the (static) information about the level which is not influenced
  by the user's progress.
  -/
  levelInfo : LevelInfo
deriving ToJson, FromJson

/--
Pack the our custom `WorkerState` on top of the normal worker monad
`Server.FileWorker.WorkerM`.
-/
abbrev WorkerM := StateT WorkerState Server.FileWorker.WorkerM

section Elab

-- -- TODO: use HashSet for allowed tactics?
-- /--
-- Find all tactics in syntax object that are forbidden according to a
-- set `allowed` of allowed tactics.
-- -/
-- partial def findForbiddenTactics (inputCtx : Parser.InputContext) (workerState : WorkerState)
--     (stx : Syntax) : Elab.Command.CommandElabM Unit := do
--   let levelInfo := workerState.levelInfo
--   -- Parse the syntax object and look for tactics and declarations.
--   match stx with
--   | .missing => return ()
--   | .node _info _kind args =>
--     -- Go inside a node.
--     for arg in args do
--       findForbiddenTactics inputCtx workerState arg
--   | .atom info val =>
--     -- Atoms might be tactic names or other keywords.
--     -- Note: We whitelisted known keywords because we cannot
--     -- distinguish keywords from tactic names.
--     let allowed := GameServer.ALLOWED_KEYWORDS
--     -- Ignore syntax elements that do not start with a letter or are listed above.
--     if 0 < val.length ∧ val.data[0]!.isAlpha ∧ not (allowed.contains val) then
--       -- Treat `simp?` and `simp!` like `simp`
--       let val := val.dropRightWhile (fun c => c == '!' || c == '?')
--       match levelInfo.tactics.find? (·.name.toString == val) with
--       | none =>
--         -- Tactic will never be introduced in the game.
--         match workerState.inventory.find? (· == val) with
--         | some _ =>
--           -- Tactic is in the inventory, allow it.
--           -- Note: This case shouldn't be possible...
--           pure ()
--         | none =>
--           -- Tactic is not in the inventory.
--           addMessageByDifficulty info s!"The tactic '{val}' is not available in this game!"
--       | some tac =>
--         -- Tactic is introduced at some point in the game.
--         if tac.disabled then
--           -- Tactic is disabled in this level.
--           addMessageByDifficulty info s!"The tactic '{val}' is disabled in this level!"
--         else if tac.locked then
--           match workerState.inventory.find? (· == val) with
--           | none =>
--             -- Tactic is marked as locked and not in the inventory.
--             addMessageByDifficulty info s!"You have not unlocked the tactic '{val}' yet!"
--           | some _ =>
--             -- Tactic is in the inventory, allow it.
--             pure ()
--   | .ident info _rawVal val _preresolved =>
--     -- Try to resolve the name
--     let ns ←
--       try resolveGlobalConst (mkIdent val)
--       -- Catch "unknown constant" error
--       catch | _ => pure []
--     for n in ns do
--       let some (.thmInfo ..) := (← getEnv).find? n
--         -- Not a theorem, no checks needed.
--         | return ()
--       if some n.toString = levelInfo.statementName then
--         -- Forbid the theorem we are proving currently
--         addMessage info inputCtx (severity := .error)
--           s!"Structural recursion: you can't use '{n}' to proof itself!"
--       let theoremsAndDefs := levelInfo.lemmas ++ levelInfo.definitions
--       match theoremsAndDefs.find? (·.name == n) with
--       | none =>
--         -- Theorem will never be introduced in this game
--         addMessageByDifficulty info s!"The theorem/definition '{n}' is not available in this game!"
--       | some thm =>
--         -- Theorem is introduced at some point in the game.
--         if thm.disabled then
--           -- Theorem is disabled in this level.
--           addMessageByDifficulty info s!"The theorem/definition '{n}' is disabled in this level!"
--         else if thm.locked then
--           match workerState.inventory.find? (· == n.toString) with
--           | none =>
--             -- Theorem is still locked.
--             addMessageByDifficulty info s!"You have not unlocked the theorem/definition '{n}' yet!"
--           | some _ =>
--             -- Theorem is in the inventory, allow it.
--             pure ()
-- where addMessageByDifficulty (info : SourceInfo) (s : MessageData) :=
--   -- See `GameServer.FileWorker.WorkerState.difficulty`. Send nothing/warnings/errors
--   -- depending on difficulty.
--   let difficulty := workerState.difficulty
--   if difficulty > 0 then
--     addMessage info inputCtx (if difficulty > 1 then .error else .warning) s
--   else pure ()

-- open Elab Meta Expr in

-- def compileProof (inputCtx : Parser.InputContext) (snap : Snapshot) (hasWidgets : Bool)
--     (couldBeEndSnap : Bool) (gameWorkerState : WorkerState)
--     (initParams : Lsp.InitializeParams) : IO Snapshot := do
--   -- Recognize end snap
--   if inputCtx.input.atEnd snap.mpState.pos ∧ couldBeEndSnap then
--     let endSnap : Snapshot := {
--       -- beginPos := snap.mpState.pos
--       stx := MyModule.mkEOI snap.mpState.pos
--       mpState := snap.mpState
--       cmdState := snap.cmdState
--       -- interactiveDiags := ← withNewInteractiveDiags snap.msgLog
--       -- tacticCache := snap.tacticCache
--     }
--     return endSnap

--   let parseResultRef ← IO.mkRef (Syntax.missing, snap.mpState)

--   let cmdStateRef ← IO.mkRef snap.cmdState
--   /- The same snapshot may be executed by different tasks. So, to make sure `elabCommandTopLevel` has exclusive
--       access to the cache, we create a fresh reference here. Before this change, the
--       following `snap.tacticCache.modify` would reset the tactic post cache while another snapshot was still using it. -/
--   -- let tacticCacheNew ← IO.mkRef (← snap.tacticCache.get)
--   let cmdCtx : Elab.Command.Context := {
--     cmdPos       := snap.endPos
--     fileName     := inputCtx.fileName
--     fileMap      := inputCtx.fileMap
--     tacticCache? := none -- some tacticCacheNew
--     snap? := none
--     cancelTk? := none
--   }
--   let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := server.stderrAsMessages.get snap.cmdState.scopes.head!.opts) <| liftM (m := BaseIO) do
--     Elab.Command.catchExceptions
--       (getResetInfoTrees *> do
--         let some level ← GameServer.getLevelByFileName? initParams inputCtx.fileName
--           | panic! s!"Level not found: {inputCtx.fileName} / {GameServer.levelIdFromFileName? initParams inputCtx.fileName}"
--         let scope := level.scope

--         -- use open namespaces and options as in the level file
--         Elab.Command.withScope (fun _ => scope) do
--           for od in scope.openDecls do
--             let .simple ns _ := od
--               | pure ()
--             activateScoped ns
--           activateScoped scope.currNamespace

--           -- parse tactics
--           let pmctx := {
--             env := ← getEnv,
--             options := scope.opts,
--             currNamespace := scope.currNamespace,
--             openDecls := scope.openDecls }
--           let (tacticStx, cmdParserState, msgLog, endOfWhitespace) :=
--             MyModule.parseTactic inputCtx pmctx snap.mpState snap.msgLog
--           modify (fun s => { s with messages := msgLog })
--           parseResultRef.set (tacticStx, cmdParserState)

--           -- Check for forbidden tactics
--           findForbiddenTactics inputCtx gameWorkerState tacticStx

--           -- Insert invisible `skip` command to make sure we always display the initial goal
--           let skip := Syntax.node (.original default 0 default endOfWhitespace) ``Lean.Parser.Tactic.skip #[]
--           -- Insert final `done` command to display unsolved goal error in the end
--           let done := Syntax.node (.synthetic cmdParserState.pos cmdParserState.pos) ``Lean.Parser.Tactic.done #[]
--           let tacticStx := (#[skip] ++ tacticStx.getArgs ++ #[done]).map (⟨.⟩)
--           let tacticStx := ← `(Lean.Parser.Tactic.tacticSeq| $[$(tacticStx)]*)

--           -- Always call `let_intros` to get rid `let` statements in the goal.
--           -- This makes the experience for the user much nicer and allows for local
--           -- definitions in the exercise.
--           let cmdStx ← `(command|
--             theorem the_theorem $(level.goal) := by {let_intros; $(⟨level.preamble⟩); $(⟨tacticStx⟩)} )
--           Elab.Command.elabCommandTopLevel cmdStx)
--       cmdCtx cmdStateRef
--   -- let postNew := (← tacticCacheNew.get).post
--   -- snap.tacticCache.modify fun _ => { pre := postNew, post := {} }
--   let mut postCmdState ← cmdStateRef.get
--   if !output.isEmpty then
--     postCmdState := {
--       postCmdState with
--       messages := postCmdState.messages.add {
--         fileName := inputCtx.fileName
--         severity := MessageSeverity.information
--         pos      := inputCtx.fileMap.toPosition snap.endPos
--         data     := output
--       }
--     }

--   let (tacticStx, cmdParserState) ← parseResultRef.get
--   if tacticStx.isMissing then throwServerError "Tactic execution went wrong. No stx found."

--   let postCmdSnap : Snapshot := {
--     -- beginPos := tacticStx.getPos?.getD 0
--     stx := tacticStx
--     mpState := cmdParserState
--     cmdState := postCmdState
--     -- interactiveDiags := ← withNewInteractiveDiags postCmdState.messages
--     -- tacticCache := (← IO.mkRef {})
--   }
--   return postCmdSnap

-- where
--   /-- Compute the current interactive diagnostics log by finding a "diff" relative to the parent
--   snapshot. We need to do this because unlike the `MessageLog` itself, interactive diags are not
--   part of the command state. -/
--   withNewInteractiveDiags (msgLog : MessageLog) : IO (PersistentArray Widget.InteractiveDiagnostic) := do
--     let newMsgCount := msgLog.msgs.size - snap.msgLog.msgs.size
--     let mut ret := snap.interactiveDiags
--     for i in List.iota newMsgCount do
--       let newMsg := msgLog.msgs.get! (msgLog.msgs.size - i)
--       ret := ret.push (← Widget.msgToInteractiveDiagnostic inputCtx.fileMap newMsg hasWidgets)
--     return ret

--   private def publishIleanInfo (method : String) (m : DocumentMeta) (hOut : FS.Stream)
--       (snaps : Array Snapshot) : IO Unit := do
--     let trees := snaps.map fun snap => snap.infoTree
--     let references ← findModuleRefs m.text trees (localVars := true) |>.toLspModuleRefs
--     let param := { version := m.version, references : LeanIleanInfoParams }
--     hOut.writeLspNotification { method, param }

--   private def publishIleanInfoUpdate : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
--     publishIleanInfo "$/lean/ileanInfoUpdate"

--   private def publishIleanInfoFinal : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
--     publishIleanInfo "$/lean/ileanInfoFinal"

--   structure GameCompletedParams where
--     uri : String
--   deriving ToJson, FromJson

-- structure GameDiagnostics where
--   diagnostics : List Diagnostic
-- deriving ToJson, FromJson

-- structure GameParams where
--   uri : String
--   diagnostics : GameDiagnostics
-- deriving ToJson, FromJson

-- -- `snap` and `initParams` are unused
-- set_option linter.unusedVariables false in

-- /-- WIP: publish diagnostics, all intermediate goals and if the game is completed. -/
-- def publishProofState (m : DocumentMeta) (snap : Snapshot) (initParams : Lsp.InitializeParams) (hOut : FS.Stream) :
--     IO Unit := do
--   -- let text := m.text

--   -- -- `snap` is the one snapshot containing the entire proof.
--   -- let mut goals : Array <| InteractiveGoalsWithHints := #[]
--   -- for pos in text.positions do
--   --   let source := text.getLineBefore pos
--   --   -- iterate over all newlines in the proof and get the goals and hints at each position
--   --   if let goalsAtResult@(_ :: _) := snap.infoTree.goalsAt? text pos then
--   --     pure ()
--   --     let goalAtPos : List <| List InteractiveGoalWithHints ← goalsAtResult.mapM
--   --       fun { ctxInfo := ci, tacticInfo := tacticInfo, useAfter := useAfter, .. } => do
--   --         -- TODO: What does this function body do?
--   --         -- let ciAfter := { ci with mctx := ti.mctxAfter }
--   --         let ci := if useAfter then
--   --             { ci with mctx := tacticInfo.mctxAfter }
--   --           else
--   --             { ci with mctx := tacticInfo.mctxBefore }
--   --         -- compute the interactive goals
--   --         let goalMvars : List MVarId ← ci.runMetaM {} do
--   --           return if useAfter then tacticInfo.goalsAfter else tacticInfo.goalsBefore

--   --         let interactiveGoals : List InteractiveGoalWithHints ← ci.runMetaM {} do
--   --           goalMvars.mapM fun goal => do
--   --             let hints ← findHints goal m initParams
--   --             let interactiveGoal ← goalToInteractive goal
--   --             return ⟨interactiveGoal, hints⟩
--   --         -- TODO: This code is way old, can it be deleted?
--   --         -- compute the goal diff
--   --         -- let goals ← ciAfter.runMetaM {} (do
--   --         --     try
--   --         --       Widget.diffInteractiveGoals useAfter ti goals
--   --         --     catch _ =>
--   --         --       -- fail silently, since this is just a bonus feature
--   --         --       return goals
--   --         -- )
--   --         return interactiveGoals
--   --     let goalAtPos : Array InteractiveGoalWithHints := ⟨goalAtPos.foldl (· ++ ·) []⟩
--   --     goals := goals.push ⟨goalAtPos, source⟩
--   --   else
--   --     -- No goals present
--   --     goals := goals.push default

--   -- -- Question: Is there a difference between the diags of this snap and the last snap?
--   -- -- Should we get the diags from there?
--   -- let diag : Array Widget.InteractiveDiagnostic := snap.interactiveDiags.toArray

--   -- -- Level is completed if there are no errors or warnings
--   -- let completed : Bool := ¬ diag.any (fun d =>
--   --   d.severity? == some .error ∨ d.severity? == some .warning)

--   -- let param : ProofState := {
--   --   steps := goals,
--   --   diagnostics := diag,
--   --   completed := completed }

--   -- TODO
--   let param := { uri := m.uri : GameCompletedParams}


--   hOut.writeLspNotification { method := "$/game/publishProofState", param }

-- /-- Checks whether game level has been completed and sends a notification to the client -/
-- def publishGameCompleted (m : DocumentMeta) (hOut : FS.Stream) (snaps : Array Snapshot) : IO Unit := do
--   -- check if there is any error or warning
--   for snap in snaps do
--     if snap.diagnostics.any fun d => d.severity? == some .error ∨ d.severity? == some .warning
--     then return
--   let param := { uri := m.uri : GameCompletedParams}
--   hOut.writeLspNotification { method := "$/game/completed", param }

-- /-- copied from `Lean.Server.FileWorker.nextCmdSnap`. -/
-- -- @[inherit_doc Lean.Server.FileWorker.nextCmdSnap] -- cannot inherit from private
-- private def nextCmdSnap (ctx : WorkerContext) (m : DocumentMeta) (cancelTk : CancelToken)
--     (gameWorkerState : WorkerState) (initParams : Lsp.InitializeParams) :
--     AsyncElabM (Option Snapshot) := do
--   cancelTk.check
--   let s ← get
--   let .some lastSnap := s.snaps.back? | panic! "empty snapshots"
--   if lastSnap.isAtEnd then
--     publishDiagnostics m lastSnap.diagnostics.toArray ctx.hOut
--     publishProgressDone m ctx.hOut
--     publishIleanInfoFinal m ctx.hOut s.snaps
--     return none
--   publishProgressAtPos m lastSnap.endPos ctx.hOut

--   -- (modified part)
--   -- Make sure that there is at least one snap after the head snap, so that
--   -- we can see the current goal even on an empty document
--   let couldBeEndSnap := s.snaps.size > 1
--   let snap ← compileProof m.mkInputContext lastSnap ctx.clientHasWidgets couldBeEndSnap
--     gameWorkerState initParams

--   set { s with snaps := s.snaps.push snap }
--   cancelTk.check
--   -- publishProofState m snap initParams ctx.hOut
--   publishDiagnostics m snap.diagnostics.toArray ctx.hOut
--   publishIleanInfoUpdate m ctx.hOut #[snap]
--   return some snap

-- -- Copied from `Lean.Server.FileWorker.unfoldCmdSnaps` using our own `nextCmdSnap`.
-- @[inherit_doc Lean.Server.FileWorker.unfoldCmdSnaps]
-- def unfoldCmdSnaps (m : DocumentMeta) (snaps : Array Snapshot) (cancelTk : CancelToken)
--     (startAfterMs : UInt32) (gameWorkerState : WorkerState)
--     : ReaderT WorkerContext IO (AsyncList ElabTaskError Snapshot) := do
--   let ctx ← read
--   let some headerSnap := snaps[0]? | panic! "empty snapshots"
--   if headerSnap.msgLog.hasErrors then
--     publishProgressAtPos m headerSnap.beginPos ctx.hOut (kind := LeanFileProgressKind.fatalError)
--     publishIleanInfoFinal m ctx.hOut #[headerSnap]
--     return AsyncList.ofList [headerSnap]
--   else
--     publishIleanInfoUpdate m ctx.hOut snaps
--     return AsyncList.ofList snaps.toList ++ AsyncList.delayed (← EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
--       IO.sleep startAfterMs
--       AsyncList.unfoldAsync (nextCmdSnap ctx m cancelTk gameWorkerState ctx.initParams) { snaps })

end Elab

section Updates

open private reportSnapshots from Lean.Server.FileWorker

/-- Given the new document, updates editable doc state. -/
def updateDocument (meta : DocumentMeta) : WorkerM Unit := do
  -- let s ← get
  -- let ctx ← read
  -- let oldDoc := (← StateT.lift get).doc
  -- oldDoc.cancelTk.set
  -- let initHeaderStx := (← StateT.lift get).initHeaderStx
  -- let (newHeaderStx, newMpState, _) ← Parser.parseHeader meta.mkInputContext
  -- let cancelTk ← CancelToken.new
  -- let headSnapTask := oldDoc.cmdSnaps.waitHead?
  -- let newSnaps ← if initHeaderStx != newHeaderStx then
  --   EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
  --     IO.sleep ctx.initParams.editDelay.toUInt32
  --     cancelTk.check
  --     IO.Process.exit 2
  -- else EIO.mapTask (ε := ElabTaskError) (t := headSnapTask) (prio := .dedicated) fun headSnap?? => do
  --   -- There is always at least one snapshot absent exceptions
  --   let some headSnap ← MonadExcept.ofExcept headSnap?? | panic! "empty snapshots"
  --   let newHeaderSnap := { headSnap with stx := newHeaderStx, mpState := newMpState }
  --   let changePos := oldDoc.meta.text.source.firstDiffPos meta.text.source
  --   -- Ignore exceptions, we are only interested in the successful snapshots
  --   let (cmdSnaps, _) ← oldDoc.cmdSnaps.getFinishedPrefix
  --   -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
  --   -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
  --   let mut validSnaps ← pure (cmdSnaps.takeWhile (fun s => s.endPos < changePos))
  --   if h : validSnaps.length ≤ 1 then
  --     validSnaps := [newHeaderSnap]
  --   else
  --     /- When at least one valid non-header snap exists, it may happen that a change does not fall
  --         within the syntactic range of that last snap but still modifies it by appending tokens.
  --         We check for this here. We do not currently handle crazy grammars in which an appended
  --         token can merge two or more previous commands into one. To do so would require reparsing
  --         the entire file. -/
  --     have : validSnaps.length ≥ 2 := Nat.gt_of_not_le h
  --     let mut lastSnap := validSnaps.getLast (by subst ·; simp at h)
  --     let preLastSnap :=
  --       have : 0 < validSnaps.length := Nat.lt_of_lt_of_le (by decide) this
  --       have : validSnaps.length - 2 < validSnaps.length := Nat.sub_lt this (by decide)
  --       validSnaps[validSnaps.length - 2]
  --     let newLastStx ← parseNextCmd meta.mkInputContext preLastSnap
  --     if newLastStx != lastSnap.stx then
  --       validSnaps := validSnaps.dropLast
  --   -- wait for a bit, giving the initial `cancelTk.check` in `nextCmdSnap` time to trigger
  --   -- before kicking off any expensive elaboration (TODO: make expensive elaboration cancelable)
  --   unfoldCmdSnaps meta validSnaps.toArray cancelTk s ctx
  --     (startAfterMs := ctx.initParams.editDelay.toUInt32)
  -- StateT.lift <| modify fun st => { st with
  --   doc := { meta := newMeta, cmdSnaps := AsyncList.delayed newSnaps, cancelTk }}

  -- from v4.14
  (← StateT.lift get).reporterCancelTk.set
  let ctx ← read
  let initSnap ← ctx.processor meta.mkInputContext
  let doc : EditableDocumentCore := {
    meta, initSnap
    diagnosticsRef := (← IO.mkRef ∅)
  }
  let reporterCancelTk ← CancelToken.new
  let reporter ← reportSnapshots ctx doc reporterCancelTk
  StateT.lift <| modify fun st => { st with doc := { doc with reporter }, reporterCancelTk }
  -- we assume version updates are monotonous and that we are on the main thread
  ctx.maxDocVersionRef.set meta.version
end Updates

section Initialization

-- def DocumentMeta.mkInputContext (doc : DocumentMeta) : Parser.InputContext where
--   input    := "" -- No header!
--   fileName := (System.Uri.fileUriToPath? doc.uri).getD doc.uri |>.toString
--   fileMap  := default

-- /-- `gameDir` and `module` were added.

-- TODO: In general this resembles little similarity with the
-- original code, and I don't know why...
-- -/
-- -- @[inherit_doc Lean.Server.FileWorker.compileHeader]
-- def compileHeader (m : DocumentMeta) (hOut : FS.Stream) (opts : Options) (hasWidgets : Bool)
--     (gameDir : String) (module : Name):
--     IO (Syntax × Task (Except Error (Snapshot × SearchPath))) := do
--   -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
--   let out ← IO.Process.output
--     { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
--   if out.exitCode != 0 then
--     throwServerError s!"Error while running Lake: {out.stderr}"

--   -- Make the paths relative to the current directory
--   let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
--   let currentDir ← IO.currentDir
--   let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

--   -- Set the search path
--   Lean.searchPathRef.set paths

--   let env ← importModules' #[{ module := `Init : Import }, { module := module : Import }]

--   -- use empty header
--   let (headerStx, headerParserState, msgLog) ← Parser.parseHeader
--     {m.mkInputContext with
--       input := ""
--       fileMap := FileMap.ofString ""}
--   (headerStx, ·) <$> EIO.asTask do
--     let mut srcSearchPath : SearchPath := paths --← initSrcSearchPath (← getBuildDir)
--     let headerEnv := env
--     let mut headerEnv := headerEnv
--     try
--       if let some path := System.Uri.fileUriToPath? m.uri then
--         headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
--     catch _ => pure ()
--     let cmdState := Elab.Command.mkState headerEnv {} opts
--     let cmdState := { cmdState with infoState := {
--       enabled := true
--       trees := #[Elab.InfoTree.context (.commandCtx {
--         env     := headerEnv
--         fileMap := m.text
--         ngen    := { namePrefix := `_worker }
--       }) (Elab.InfoTree.node
--           (Elab.Info.ofCommandInfo { elaborator := `header, stx := headerStx })
--           (headerStx[1].getArgs.toList.map (fun importStx =>
--             Elab.InfoTree.node (Elab.Info.ofCommandInfo {
--               elaborator := `import
--               stx := importStx
--             }) #[].toPArray'
--           )).toPArray'
--       )].toPArray'
--     }}
--     let headerSnap := {
--       beginPos := 0
--       stx := headerStx
--       mpState := {} -- was `headerParserState`
--       cmdState := cmdState
--       interactiveDiags := ← cmdState.messages.msgs.mapM (Widget.msgToInteractiveDiagnostic m.text · hasWidgets)
--       tacticCache := (← IO.mkRef {})
--     }
--     publishDiagnostics m headerSnap.diagnostics.toArray hOut
--     return (headerSnap, srcSearchPath)

open private mkImportClosureNotification reportSnapshots from Lean.Server.FileWorker

/-- Copied from `Lean.Server.FileWorker.initializeWorker`. Added `gameDir` and
`gameWorkerState` arguments and use custom `unfoldCmdSnaps`. -/
-- @[inherit_doc Lean.Server.FileWorker.initializeWorker]
def initializeWorker (meta : DocumentMeta) (o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
    (gameDir : String) (gameWorkerState : WorkerState)
    : IO (WorkerContext × Server.FileWorker.WorkerState) := do
  let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
-- let (headerStx, headerTask) ← compileHeader meta o opts (hasWidgets := clientHasWidgets)
--   (gameDir := gameDir) (module := gameWorkerState.levelInfo.module)
-- let cancelTk ← CancelToken.new
  let maxDocVersionRef ← IO.mkRef 0
  let freshRequestIdRef ← IO.mkRef (0 : Int)
  let chanIsProcessing ← IO.Channel.new
  let stickyDiagnosticsRef ← IO.mkRef ∅
  let chanOut ← mkLspOutputChannel maxDocVersionRef chanIsProcessing
  let srcSearchPathPromise ← IO.Promise.new

  let processor := Language.Lean.process (setupImports meta opts chanOut srcSearchPathPromise)
  let processor ← Language.mkIncrementalProcessor processor
  let initSnap ← processor meta.mkInputContext
  let _ ← IO.mapTask (t := srcSearchPathPromise.result) fun srcSearchPath => do
    let importClosure := getImportClosure? initSnap
    let importClosure ← importClosure.filterMapM (documentUriFromModule srcSearchPath ·)
    chanOut.send <| mkImportClosureNotification importClosure
  let ctx := {
    chanOut
    hLog := e
    initParams
    processor
    clientHasWidgets
    maxDocVersionRef
    freshRequestIdRef
    chanIsProcessing
    cmdlineOpts := opts
    stickyDiagnosticsRef
  }
-- let cmdSnaps ← EIO.mapTask (t := headerTask) (match · with
--   | Except.ok (s, _) => unfoldCmdSnaps meta #[s] cancelTk gameWorkerState ctx (startAfterMs := 0)
--   | Except.error e   => throw (e : ElabTaskError))
-- let doc : EditableDocument := { meta, cmdSnaps := AsyncList.delayed cmdSnaps, cancelTk }
  let doc : EditableDocumentCore := {
    meta, initSnap
    diagnosticsRef := (← IO.mkRef ∅)
  }
  let reporterCancelTk ← CancelToken.new
  let reporter ← reportSnapshots ctx doc reporterCancelTk
-- return (ctx, {
--   doc                := doc
--   initHeaderStx      := headerStx
--   currHeaderStx      := headerStx
--   importCachingTask? := none
--   pendingRequests    := RBMap.empty
--   rpcSessions        := RBMap.empty
-- })
    return (ctx, {
    doc := { doc with reporter }
    reporterCancelTk
    srcSearchPathTask  := srcSearchPathPromise.result
    pendingRequests    := RBMap.empty
    rpcSessions        := RBMap.empty
    importCachingTask? := none
  })
where
  /-- Creates an LSP message output channel along with a reader that sends out read messages on
      the output FS stream after discarding outdated notifications. This is the only component of
      the worker with access to the output stream, so we can synchronize messages from parallel
      elaboration tasks here. -/
  mkLspOutputChannel maxDocVersion chanIsProcessing : IO (IO.Channel JsonRpc.Message) := do
    let chanOut ← IO.Channel.new
    let _ ← chanOut.forAsync (prio := .dedicated) fun msg => do
      -- discard outdated notifications; note that in contrast to responses, notifications can
      -- always be silently discarded
      let version? : Option Int := do match msg with
        | .notification "textDocument/publishDiagnostics" (some params) =>
          let params : PublishDiagnosticsParams ← fromJson? (toJson params) |>.toOption
          params.version?
        | .notification "$/lean/fileProgress" (some params) =>
          let params : LeanFileProgressParams ← fromJson? (toJson params) |>.toOption
          params.textDocument.version?
        | _ => none
      if let some version := version? then
        if version < (← maxDocVersion.get) then
          return
        -- note that because of `server.reportDelayMs`, we cannot simply set `maxDocVersion` here
        -- as that would allow outdated messages to be reported until the delay is over
      o.writeLspMessage msg |>.catchExceptions (fun _ => pure ())
      if let .notification "$/lean/fileProgress" (some params) := msg then
        if let some (params : LeanFileProgressParams) := fromJson? (toJson params) |>.toOption then
          chanIsProcessing.send (! params.processing.isEmpty)
    return chanOut

  getImportClosure? (snap : Language.Lean.InitialSnapshot) : Array Name := Id.run do
    let some snap := snap.result?
      | return #[]
    let some snap ← snap.processedSnap.get.result?
      | return #[]
    let importClosure := snap.cmdState.env.allImportedModuleNames
    return importClosure

end Initialization

section NotificationHandling

/-- Copied from `Lean.Server.FileWorker.handleDidChange` but with our custom `WorkerM` and
`updateDocument` -/
-- @[inherit_doc Lean.Server.FileWorker.handleDidChange]
def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
  let docId := p.textDocument
  let changes := p.contentChanges
  let oldDoc := (← StateT.lift get).doc
  let newVersion := docId.version?.getD 0
  if ¬ changes.isEmpty then
    let newDocText := foldDocumentChanges changes oldDoc.meta.text
    -- modification: set the `DependencyBuildMode` from
    -- `oldDoc.meta.dependencyBuildMode` to `.always`
    updateDocument ⟨docId.uri, newVersion, newDocText, .always⟩

end NotificationHandling

section MessageHandling

/--
Modified notification handler.

Compare to `Lean.Server.FileWorker.handleNotification`.
We use the modified `WorkerM` and use our custom `handleDidChange`.
-/
def handleNotification (method : String) (params : Json) : WorkerM Unit := do
  let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
    (StateT.lift <| parseParams paramType params) >>= handler
  match method with
  -- modified `textDocument/didChange`, using a custom `handleDidChange`
  | "textDocument/didChange" => handle DidChangeTextDocumentParams (handleDidChange)
  -- unmodified
  | "$/cancelRequest"        => handle CancelParams (handleCancelRequest ·)
  | "$/lean/staleDependency" => handle Lsp.LeanStaleDependencyParams (handleStaleDependency ·)
  | "$/lean/rpc/release"     => handle RpcReleaseParams (handleRpcRelease ·)
  | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams (handleRpcKeepAlive ·)
  | _                        => throwServerError s!"Got unsupported notification method: {method}"

end MessageHandling

section MainLoop

variable (hIn : FS.Stream) in
/--
The main-loop. Copied from `Lean.Server.FileWorker.mainLoop`. Use custom `WorkerM` as well
as custom `handleNotification`.
-/
--@[inherit_doc Lean.Server.FileWorker.mainLoop]
partial def mainLoop : WorkerM Unit := do
  -- let ctx ← read
  let mut st ← StateT.lift get
  let msg ← hIn.readLspMessage
  let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
      : IO PendingRequestMap := do
    if (← hasFinished task) then
      if let Except.error e := task.get then
        throwServerError s!"Failed responding to request {id}: {e}"
      pure <| acc.erase id
    else pure acc
  let pendingRequests ← st.pendingRequests.foldM (fun acc id task => filterFinishedTasks acc id task) st.pendingRequests
  st := { st with pendingRequests }
  for (id, seshRef) in st.rpcSessions do
    let sesh ← seshRef.get
    if (← sesh.hasExpired) then
      st := { st with rpcSessions := st.rpcSessions.erase id }
  set st
  match msg with
  | Message.request id method (some params) =>
    handleRequest id method (toJson params)
    mainLoop
  | Message.notification "exit" none =>
    return
  | Message.notification method (some params) =>
    handleNotification method (toJson params) -- modified function used
    mainLoop
  | Message.response id result =>
    handleResponse id result
    mainLoop
  | Message.responseError .. =>
    mainLoop
  | _ => throwServerError s!"Got invalid JSON-RPC message: {toJson msg}"

end MainLoop

def getGameWorkerState (gameDir : String) (initParams : Request Game.InitializeParams) (meta : DocumentMeta) : IO WorkerState := do

  let game ← loadGameData gameDir
  -- TODO: We misuse the `rootUri` field to the gameName
  let rootUri? : Option String := some (toString game.name)
  let initParams' := {initParams.param.toLeanInternal with rootUri?}
  let some (levelId : LevelId) := GameServer.levelIdFromFileName?
      initParams' meta.mkInputContext.fileName
    | throwServerError s!"Could not determine level ID: {meta.mkInputContext.fileName}"
  let levelInfo ← loadLevelData gameDir levelId.world levelId.level
  let some initializationOptions := initParams.param.initializationOptions?
    | throwServerError "no initialization options found"
  let gameWorkerState : WorkerState := {
    inventory := initializationOptions.inventory
    difficulty := initializationOptions.difficulty
    levelInfo
  }
  return gameWorkerState

/-- Modified from `Lean.Server.FileWorker.initAndRunWorker`.
Added `gameDir` argument, -/
-- @[inherit_doc Lean.Server.FileWorker.initAndRunWorker]
def initAndRunWorker (i o e : FS.Stream) (opts : Options) (gameDir : String) : IO Unit := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" Game.InitializeParams

  -- BIG MODIFICATION
  o.writeLspResponse {
    id     := initParams.id
    result := {
      capabilities := Watchdog.mkLeanServerCapabilities
      serverInfo?  := some {
        name     := "Lean 4 Game Server"
        version? := "0.1.1"
      }
      : InitializeResult
    }
  }
  discard $ i.readLspNotificationAs "initialized" InitializedParams

  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let doc := param.textDocument
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.crlfToLf.toFileMap, .always⟩ -- modification: using `.always`
  let e := e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e

  let gameWorkerState ← getGameWorkerState gameDir initParams meta





    -- BIG MODIFICATION

    -- let (ctx, st) ← initializeWorker meta i o e initParams opts gameDir gameWorkerState
    -- -- Run the main loop
    -- let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) <|
    --   StateT.run (s := gameWorkerState) <| (mainLoop)

  let (ctx, st) ← try
    initializeWorker meta o e initParams.param.toLeanInternal opts gameDir gameWorkerState
  catch err =>
    writeErrorDiag meta err
    throw err
  StateRefT'.run' (s := st) <| ReaderT.run (r := ctx) <| StateT.run' (s := gameWorkerState) do
    try
      let refreshTask ← StateT.lift runRefreshTask
      mainLoop i
      IO.cancel refreshTask
    catch err =>
      let st ← StateT.lift get
      writeErrorDiag st.doc.meta err
      throw err
where
  writeErrorDiag (meta : DocumentMeta) (err : Error) : IO Unit := do
    o.writeLspMessage <| mkPublishDiagnosticsNotification meta #[{
      range := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩,
      fullRange? := some ⟨⟨0, 0⟩, meta.text.utf8PosToLspPos meta.text.source.endPos⟩
      severity? := DiagnosticSeverity.error
      message := err.toString }]

/--
The main function. Simply wrapping `initAndRunWorker`.

Copied from `Lean.Server.FileWorker.workerMain`. We add `args` as an argument to pass on
the `gameDir`.

TODO: The first arg `args[0]` is always expected to be `--server`. We could drop this completely.
-/
-- @[inherit_doc Lean.Server.FileWorker.workerMain]
def workerMain (opts : Options) (args : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let some gameDir := args[1]? | throwServerError "Expected second argument: gameDir"
    initAndRunWorker i o e opts gameDir
    o.flush
    e.flush
    IO.Process.exit 0
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    IO.Process.exit 1

end GameServer.FileWorker
