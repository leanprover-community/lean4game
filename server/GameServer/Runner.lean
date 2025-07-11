import Lean
import GameServer.RpcHandlers
import GameServer.SaveData
import GameServer.Tactic.LetIntros


open Lean Meta Elab Command

/-- Define the statement of the current level. -/
elab "Runner" gameId:str worldId:str levelId:num difficulty:num inventory:term val:declVal : command => do

  let game := gameId.getString
  let world := worldId.getString
  let level := levelId.getNat
  let difficulty := difficulty.getNat
  -- let inventory := inventory.getExpr

  -- extract the `tacticSeq` from `val` in order to add `let_intros` in front.
  let tacticStx : TSyntax `Lean.Parser.Tactic.tacticSeq := match val with
  | `(Parser.Command.declVal| := by $proof) => proof
  | _ => panic "expected `:= by`"

  let some level ← getLevel? {game := game, world := world, level := level}
    | panic! "Level not found"

  let thmStatement ← `(command|
    theorem the_theorem $(level.goal) := by {let_intros; $(⟨level.preamble⟩); $(⟨tacticStx⟩)} )
  elabCommand thmStatement




--TODO: Integrate the following material from the old FileWorker

/--
Collection of items which are considered unlocked.
Tactics and theorems are mixed together.
-/
def inventory : Array String := #[]
/--
Difficulty determines whether tactics/theorems can be locked.
* 0: do not check
* 1: give warnings when locked items are used
* 2: give errors when locked items are used
-/
def difficulty : Nat := 0


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

  pos := s.pos
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

namespace GameServer.FileWorker


open Lean
open Lean.Server
open Lean.Server.FileWorker
open Lsp
open IO
open Snapshots
open JsonRpc

def gameDir := "."

def levelId : LevelId := {
  game := "Game",
  world := "DemoWorld",
  level := 1
}

/--
Pack the our custom `WorkerState` on top of the normal worker monad
`Server.FileWorker.WorkerM`.
-/
abbrev WorkerM := StateT WorkerState Server.FileWorker.WorkerM

section Elab

/-- Add a message. use `(severity := .warning)` to specify the severity-/
def addMessage (info : SourceInfo) (inputCtx : Parser.InputContext)
    (severity := MessageSeverity.warning) (s : MessageData) :
    Elab.Command.CommandElabM Unit := do
  modify fun st => { st with
    messages := st.messages.add {
      fileName := inputCtx.fileName
      severity := severity
      pos      := inputCtx.fileMap.toPosition (info.getPos?.getD 0)
      data     := s }}

-- TODO: use HashSet for allowed tactics?
/--
Find all tactics in syntax object that are forbidden according to a
set `allowed` of allowed tactics.
-/
partial def findForbiddenTactics (inputCtx : Parser.InputContext) (workerState : WorkerState)
    (stx : Syntax) : Elab.Command.CommandElabM Unit := do
  let levelInfo ← loadLevelData gameDir levelId.world levelId.level
  -- Parse the syntax object and look for tactics and declarations.
  match stx with
  | .missing => return ()
  | .node _info _kind args =>
    -- Go inside a node.
    for arg in args do
      findForbiddenTactics inputCtx workerState arg
  | .atom info val =>
    -- Atoms might be tactic names or other keywords.
    -- Note: We whitelisted known keywords because we cannot
    -- distinguish keywords from tactic names.
    let allowed := GameServer.ALLOWED_KEYWORDS
    -- Ignore syntax elements that do not start with a letter or are listed above.
    if 0 < val.length ∧ val.data[0]!.isAlpha ∧ not (allowed.contains val) then
      -- Treat `simp?` and `simp!` like `simp`
      let val := val.dropRightWhile (fun c => c == '!' || c == '?')
      match levelInfo.tactics.find? (·.name.toString == val) with
      | none =>
        -- Tactic will never be introduced in the game.
        match inventory.find? (· == val) with
        | some _ =>
          -- Tactic is in the inventory, allow it.
          -- Note: This case shouldn't be possible...
          pure ()
        | none =>
          -- Tactic is not in the inventory.
          addMessageByDifficulty info s!"The tactic '{val}' is not available in this game!"
      | some tac =>
        -- Tactic is introduced at some point in the game.
        if tac.disabled then
          -- Tactic is disabled in this level.
          addMessageByDifficulty info s!"The tactic '{val}' is disabled in this level!"
        else if tac.locked then
          match inventory.find? (· == val) with
          | none =>
            -- Tactic is marked as locked and not in the inventory.
            addMessageByDifficulty info s!"You have not unlocked the tactic '{val}' yet!"
          | some _ =>
            -- Tactic is in the inventory, allow it.
            pure ()
  | .ident info _rawVal val _preresolved =>
    -- Try to resolve the name
    let ns ←
      try resolveGlobalConst (mkIdent val)
      -- Catch "unknown constant" error
      catch | _ => pure []
    for n in ns do
      let some (.thmInfo ..) := (← getEnv).find? n
        -- Not a theorem, no checks needed.
        | return ()
      if some n = levelInfo.statementName then
        -- Forbid the theorem we are proving currently
        addMessage info inputCtx (severity := .error)
          s!"Structural recursion: you can't use '{n}' to proof itself!"
      let theoremsAndDefs := levelInfo.lemmas ++ levelInfo.definitions
      match theoremsAndDefs.find? (·.name == n) with
      | none =>
        -- Theorem will never be introduced in this game
        addMessageByDifficulty info s!"The theorem/definition '{n}' is not available in this game!"
      | some thm =>
        -- Theorem is introduced at some point in the game.
        if thm.disabled then
          -- Theorem is disabled in this level.
          addMessageByDifficulty info s!"The theorem/definition '{n}' is disabled in this level!"
        else if thm.locked then
          match inventory.find? (· == n.toString) with
          | none =>
            -- Theorem is still locked.
            addMessageByDifficulty info s!"You have not unlocked the theorem/definition '{n}' yet!"
          | some _ =>
            -- Theorem is in the inventory, allow it.
            pure ()

where addMessageByDifficulty (info : SourceInfo) (s : MessageData) :=
  -- See `GameServer.FileWorker.WorkerState.difficulty`. Send nothing/warnings/errors
  -- depending on difficulty.
  let difficulty := difficulty
  if difficulty > 0 then
    addMessage info inputCtx (if difficulty > 1 then .error else .warning) s
  else pure ()

open Elab Meta Expr in

def compileProof (inputCtx : Parser.InputContext) (snap : Snapshot) (hasWidgets : Bool)
    (couldBeEndSnap : Bool) (gameWorkerState : WorkerState)
    (initParams : Lsp.InitializeParams) : IO Snapshot := do
  -- Recognize end snap
  if inputCtx.input.atEnd snap.mpState.pos ∧ couldBeEndSnap then
    let endSnap : Snapshot := {
      beginPos := snap.mpState.pos
      stx := mkEOI snap.mpState.pos
      mpState := snap.mpState
      cmdState := snap.cmdState
      interactiveDiags := ← withNewInteractiveDiags snap.msgLog
      tacticCache := snap.tacticCache
    }
    return endSnap

  let parseResultRef ← IO.mkRef (Syntax.missing, snap.mpState)

  let cmdStateRef ← IO.mkRef snap.cmdState
  /- The same snapshot may be executed by different tasks. So, to make sure `elabCommandTopLevel` has exclusive
      access to the cache, we create a fresh reference here. Before this change, the
      following `snap.tacticCache.modify` would reset the tactic post cache while another snapshot was still using it. -/
  let tacticCacheNew ← IO.mkRef (← snap.tacticCache.get)
  let cmdCtx : Elab.Command.Context := {
    cmdPos       := snap.endPos
    fileName     := inputCtx.fileName
    fileMap      := inputCtx.fileMap
    tacticCache? := some tacticCacheNew
  }
  let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := server.stderrAsMessages.get snap.cmdState.scopes.head!.opts) <| liftM (m := BaseIO) do
    Elab.Command.catchExceptions
      (getResetInfoTrees *> do
        let some level ← GameServer.getLevelByFileName? initParams inputCtx.fileName
          | panic! s!"Level not found: {inputCtx.fileName} / {GameServer.levelIdFromFileName? initParams inputCtx.fileName}"
        let scope := level.scope

        -- use open namespaces and options as in the level file
        Elab.Command.withScope (fun _ => scope) do
          for od in scope.openDecls do
            let .simple ns _ := od
              | pure ()
            activateScoped ns
          activateScoped scope.currNamespace

          -- parse tactics
          let pmctx := {
            env := ← getEnv,
            options := scope.opts,
            currNamespace := scope.currNamespace,
            openDecls := scope.openDecls }
          let (tacticStx, cmdParserState, msgLog, endOfWhitespace) :=
            parseTactic inputCtx pmctx snap.mpState snap.msgLog
          modify (fun s => { s with messages := msgLog })
          parseResultRef.set (tacticStx, cmdParserState)

          -- Check for forbidden tactics
          findForbiddenTactics inputCtx gameWorkerState tacticStx

          -- Insert invisible `skip` command to make sure we always display the initial goal
          let skip := Syntax.node (.original default 0 default endOfWhitespace) ``Lean.Parser.Tactic.skip #[]
          -- Insert final `done` command to display unsolved goal error in the end
          let done := Syntax.node (.synthetic cmdParserState.pos cmdParserState.pos) ``Lean.Parser.Tactic.done #[]
          let tacticStx := (#[skip] ++ tacticStx.getArgs ++ #[done]).map (⟨.⟩)
          let tacticStx := ← `(Lean.Parser.Tactic.tacticSeq| $[$(tacticStx)]*)

          -- Always call `let_intros` to get rid `let` statements in the goal.
          -- This makes the experience for the user much nicer and allows for local
          -- definitions in the exercise.
          let cmdStx ← `(command|
            theorem the_theorem $(level.goal) := by {let_intros; $(⟨level.preamble⟩); $(⟨tacticStx⟩)} )
          Elab.Command.elabCommandTopLevel cmdStx)
      cmdCtx cmdStateRef
  let postNew := (← tacticCacheNew.get).post
  snap.tacticCache.modify fun _ => { pre := postNew, post := {} }
  let mut postCmdState ← cmdStateRef.get
  if !output.isEmpty then
    postCmdState := {
      postCmdState with
      messages := postCmdState.messages.add {
        fileName := inputCtx.fileName
        severity := MessageSeverity.information
        pos      := inputCtx.fileMap.toPosition snap.endPos
        data     := output
      }
    }

  let (tacticStx, cmdParserState) ← parseResultRef.get
  if tacticStx.isMissing then throwServerError "Tactic execution went wrong. No stx found."

  let postCmdSnap : Snapshot := {
    beginPos := tacticStx.getPos?.getD 0
    stx := tacticStx
    mpState := cmdParserState
    cmdState := postCmdState
    interactiveDiags := ← withNewInteractiveDiags postCmdState.messages
    tacticCache := (← IO.mkRef {})
  }
  return postCmdSnap

where
  /-- Compute the current interactive diagnostics log by finding a "diff" relative to the parent
  snapshot. We need to do this because unlike the `MessageLog` itself, interactive diags are not
  part of the command state. -/
  withNewInteractiveDiags (msgLog : MessageLog) : IO (PersistentArray Widget.InteractiveDiagnostic) := do
    let newMsgCount := msgLog.msgs.size - snap.msgLog.msgs.size
    let mut ret := snap.interactiveDiags
    for i in List.iota newMsgCount do
      let newMsg := msgLog.msgs.get! (msgLog.msgs.size - i)
      ret := ret.push (← Widget.msgToInteractiveDiagnostic inputCtx.fileMap newMsg hasWidgets)
    return ret
