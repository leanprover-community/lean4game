/- This file is mostly copied from `Lean/Server/FileWorker.lean`. -/

import Lean
import GameServer.EnvExtensions
import GameServer.RpcHandlers

import Lean.Server.FileWorker

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
  (mps : ModuleParserState) (messages : MessageLog) (couldBeEndSnap : Bool) :
    Syntax × ModuleParserState × MessageLog × String.Pos := Id.run do
  let mut pos := mps.pos
  let mut recovering := mps.recovering
  let mut messages := messages
  let mut stx := Syntax.missing  -- will always be assigned below
  if inputCtx.input.atEnd pos ∧ couldBeEndSnap then
    stx := mkEOI pos
    return (stx, { pos, recovering }, messages, 0)

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

end MyModule

namespace MyServer.FileWorker
open Lean
open Lean.Server
open Lean.Server.FileWorker
open Lsp
open IO
open Snapshots
open JsonRpc

section Elab

-- TODO: use HashSet for allowed tactics?
/-- Find all tactics in syntax object that are forbidden according to a
set `allowed` of allowed tactics. -/
partial def findForbiddenTactics (inputCtx : Parser.InputContext) (level : GameLevel) (stx : Syntax)
  : Elab.Command.CommandElabM Unit := do
  match stx with
  | .missing => return ()
  | .node info kind args =>
    for arg in args do
      findForbiddenTactics inputCtx level arg
  | .atom info val =>
    -- ignore syntax elements that do not start with a letter
    -- and ignore "with" keyword
    if 0 < val.length ∧ val.data[0]!.isAlpha ∧ val != "with" then
      if ¬ ((level.tactics.map (·.name.toString))).contains val then
        addErrorMessage info s!"You have not unlocked the tactic '{val}' yet!"
      else if level.disabledTactics.contains val
        ∨ (¬ level.onlyTactics.isEmpty ∧ ¬ level.onlyTactics.contains val)then
        addErrorMessage info s!"The tactic '{val}' is disabled in this level!"
  | .ident info rawVal val preresolved => return ()
where addErrorMessage (info : SourceInfo) (s : MessageData) :=
  modify fun st => { st with
    messages := st.messages.add {
      fileName := inputCtx.fileName
      severity := MessageSeverity.error
      pos      := inputCtx.fileMap.toPosition (info.getPos?.getD 0)
      data     := s
    }
  }

open Elab Meta Expr in
def compileProof (inputCtx : Parser.InputContext) (snap : Snapshot) (hasWidgets : Bool) (couldBeEndSnap : Bool) : IO Snapshot := do
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (tacticStx, cmdParserState, msgLog, endOfWhitespace) :=
    MyModule.parseTactic inputCtx pmctx snap.mpState snap.msgLog couldBeEndSnap
  let cmdPos := tacticStx.getPos?.getD 0
  if Parser.isTerminalCommand tacticStx then
    let endSnap : Snapshot := {
      beginPos := cmdPos
      stx := tacticStx
      mpState := cmdParserState
      cmdState := snap.cmdState
      interactiveDiags := ← withNewInteractiveDiags msgLog
      tacticCache := snap.tacticCache
    }
    return endSnap
  else
    let cmdStateRef ← IO.mkRef { snap.cmdState with messages := msgLog }
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
    let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := server.stderrAsMessages.get scope.opts) <| liftM (m := BaseIO) do
      Elab.Command.catchExceptions
        (getResetInfoTrees *> do
          let level ← GameServer.getLevelByFileName inputCtx.fileName

          -- Check for forbidden tactics
          findForbiddenTactics inputCtx level tacticStx

          -- Insert invisible `skip` command to make sure we always display the initial goal
          let skip := Syntax.node (.original default 0 default endOfWhitespace) ``Lean.Parser.Tactic.skip #[]
          -- Insert final `done` command to display unsolved goal error in the end
          let done := Syntax.node (.synthetic cmdParserState.pos cmdParserState.pos) ``Lean.Parser.Tactic.done #[]
          let tacticStx := (#[skip] ++ tacticStx.getArgs ++ #[done]).map (⟨.⟩)
          let tacticStx := ← `(Lean.Parser.Tactic.tacticSeq| $[$(tacticStx)]*)

          let cmdStx ← `(command|
            set_option tactic.hygienic false in
            theorem the_theorem $(level.goal) := by {$(⟨tacticStx⟩)} )
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

    let postCmdSnap : Snapshot := {
      beginPos := cmdPos
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

  private def publishIleanInfo (method : String) (m : DocumentMeta) (hOut : FS.Stream)
      (snaps : Array Snapshot) : IO Unit := do
    let trees := snaps.map fun snap => snap.infoTree
    let references := findModuleRefs m.text trees (localVars := true)
    let param := { version := m.version, references : LeanIleanInfoParams }
    hOut.writeLspNotification { method, param }

  private def publishIleanInfoUpdate : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoUpdate"

  private def publishIleanInfoFinal : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoFinal"

  structure GameCompletedParams where
    uri : String
  deriving ToJson, FromJson

  /-- Checks whether game level has been completed and sends a notification to the client -/
  def publishGameCompleted (m : DocumentMeta) (hOut : FS.Stream) (snaps : Array Snapshot) : IO Unit := do
    -- check if there is any error or warning
    for snap in snaps do
      if snap.diagnostics.any fun d => d.severity? == some .error ∨ d.severity? == some .warning
      then return
    let param := { uri := m.uri : GameCompletedParams}
    hOut.writeLspNotification { method := "$/game/completed", param }

  /-- Elaborates the next command after `parentSnap` and emits diagnostics into `hOut`. -/
  private def nextSnap (ctx : WorkerContext) (m : DocumentMeta) (cancelTk : CancelToken)
      : AsyncElabM (Option Snapshot) := do
    cancelTk.check
    let s ← get
    let .some lastSnap := s.snaps.back? | panic! "empty snapshots"
    if lastSnap.isAtEnd then
      publishGameCompleted m ctx.hOut s.snaps
      publishDiagnostics m lastSnap.diagnostics.toArray ctx.hOut
      publishProgressDone m ctx.hOut
      -- This will overwrite existing ilean info for the file, in case something
      -- went wrong during the incremental updates.
      publishIleanInfoFinal m ctx.hOut s.snaps
      return none
    publishProgressAtPos m lastSnap.endPos ctx.hOut
    -- Make sure that there is at least one snap after the head snap, so that
    -- we can see the current goal even on an empty document
    let couldBeEndSnap := s.snaps.size > 1
    let snap ← compileProof m.mkInputContext lastSnap ctx.clientHasWidgets couldBeEndSnap
    set { s with snaps := s.snaps.push snap }
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
    /- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
      while prefering newer versions over old ones. The former is necessary because we do
      not explicitly clear older diagnostics, while the latter is necessary because we do
      not guarantee that diagnostics are emitted in order. Specifically, it may happen that
      we interrupted this elaboration task right at this point and a newer elaboration task
      emits diagnostics, after which we emit old diagnostics because we did not yet detect
      the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
      because we cannot guarantee that no further diagnostics are emitted after clearing
      them. -/
    -- NOTE(WN): this is *not* redundent even if there are no new diagnostics in this snapshot
    -- because empty diagnostics clear existing error/information squiggles. Therefore we always
    -- want to publish in case there was previously a message at this position.
    publishDiagnostics m snap.diagnostics.toArray ctx.hOut
    publishIleanInfoUpdate m ctx.hOut #[snap]
    return some snap

  /-- Elaborates all commands after the last snap (at least the header snap is assumed to exist), emitting the diagnostics into `hOut`. -/
  def unfoldSnaps (m : DocumentMeta) (snaps : Array Snapshot) (cancelTk : CancelToken) (startAfterMs : UInt32)
      : ReaderT WorkerContext IO (AsyncList ElabTaskError Snapshot) := do
    let ctx ← read
    let some headerSnap := snaps[0]? | panic! "empty snapshots"
    if headerSnap.msgLog.hasErrors then
      -- Treat header processing errors as fatal so users aren't swamped with
      -- followup errors
      publishProgressAtPos m headerSnap.beginPos ctx.hOut (kind := LeanFileProgressKind.fatalError)
      publishIleanInfoFinal m ctx.hOut #[headerSnap]
      return AsyncList.ofList [headerSnap]
    else
      -- This will overwrite existing ilean info for the file since this has a
      -- higher version number.
      publishIleanInfoUpdate m ctx.hOut snaps
      return AsyncList.ofList snaps.toList ++ AsyncList.delayed (← EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
        IO.sleep startAfterMs
        AsyncList.unfoldAsync (nextSnap ctx m cancelTk) { snaps })

end Elab

section Updates

/-- Given the new document, updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) : WorkerM Unit := do
    let ctx ← read
    let oldDoc := (←get).doc
    oldDoc.cancelTk.set
    let initHeaderStx := (← get).initHeaderStx
    let (newHeaderStx, newMpState, _) ← Parser.parseHeader newMeta.mkInputContext
    let cancelTk ← CancelToken.new
    let headSnapTask := oldDoc.cmdSnaps.waitHead?
    let newSnaps ← if initHeaderStx != newHeaderStx then
      EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
        IO.sleep ctx.initParams.editDelay.toUInt32
        cancelTk.check
        IO.Process.exit 2
    else EIO.mapTask (ε := ElabTaskError) (t := headSnapTask) (prio := .dedicated) fun headSnap?? => do
      -- There is always at least one snapshot absent exceptions
      let some headSnap ← MonadExcept.ofExcept headSnap?? | panic! "empty snapshots"
      let newHeaderSnap := { headSnap with stx := newHeaderStx, mpState := newMpState }
      let changePos := oldDoc.meta.text.source.firstDiffPos newMeta.text.source
      -- Ignore exceptions, we are only interested in the successful snapshots
      let (cmdSnaps, _) ← oldDoc.cmdSnaps.getFinishedPrefix
      -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
      -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
      let mut validSnaps ← pure (cmdSnaps.takeWhile (fun s => s.endPos < changePos))
      if h : validSnaps.length ≤ 1 then
        validSnaps := [newHeaderSnap]
      else
        /- When at least one valid non-header snap exists, it may happen that a change does not fall
           within the syntactic range of that last snap but still modifies it by appending tokens.
           We check for this here. We do not currently handle crazy grammars in which an appended
           token can merge two or more previous commands into one. To do so would require reparsing
           the entire file. -/
        have : validSnaps.length ≥ 2 := Nat.gt_of_not_le h
        let mut lastSnap := validSnaps.getLast (by subst ·; simp at h)
        let preLastSnap :=
          have : 0 < validSnaps.length := Nat.lt_of_lt_of_le (by decide) this
          have : validSnaps.length - 2 < validSnaps.length := Nat.sub_lt this (by decide)
          validSnaps[validSnaps.length - 2]
        let newLastStx ← parseNextCmd newMeta.mkInputContext preLastSnap
        if newLastStx != lastSnap.stx then
          validSnaps := validSnaps.dropLast
      -- wait for a bit, giving the initial `cancelTk.check` in `nextCmdSnap` time to trigger
      -- before kicking off any expensive elaboration (TODO: make expensive elaboration cancelable)
      unfoldSnaps newMeta validSnaps.toArray cancelTk ctx
        (startAfterMs := ctx.initParams.editDelay.toUInt32)
    modify fun st => { st with doc := { meta := newMeta, cmdSnaps := AsyncList.delayed newSnaps, cancelTk } }

end Updates

section Initialization


  def DocumentMeta.mkInputContext (doc : DocumentMeta) : Parser.InputContext where
    input    := "" -- No header!
    fileName := (System.Uri.fileUriToPath? doc.uri).getD doc.uri |>.toString
    fileMap  := default

  -- TODO: Duplicate in Watchdog?
  def createEnv : IO (Environment × SearchPath) := do
    let gameDir := "../../../testgame"

    -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
    let out ← IO.Process.output
      { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
    if out.exitCode != 0 then
      throwServerError s!"Error while running Lake: {out.stderr}"

    -- Make the paths relative to the current directory
    let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
    let currentDir ← IO.currentDir
    let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

    -- Set the search path
    Lean.searchPathRef.set paths

    let gameName := `TestGame
    let env ← importModules [{ module := `Init : Import }, { module := gameName : Import }] {} 0
    return (env, paths)

  -- def compileHeader (m : DocumentMeta) (hOut : FS.Stream) (opts : Options) (hasWidgets : Bool)
  --     : IO (Snapshot × SearchPath) := do
  --   let mut (headerEnv, paths) ← createEnv
  --   try
  --     if let some path := System.Uri.fileUriToPath? m.uri then
  --       headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
  --   catch _ => pure ()
  --   let cmdState := Elab.Command.mkState headerEnv {} opts
  --   let cmdState := { cmdState with infoState := {
  --     enabled := true
  --     trees := #[Elab.InfoTree.context ({
  --       env     := headerEnv
  --       fileMap := m.text
  --       ngen    := { namePrefix := `_worker }
  --     }) (Elab.InfoTree.node
  --         (Elab.Info.ofCommandInfo { elaborator := `header, stx := Syntax.missing })
  --         #[].toPArray'
  --     )].toPArray'
  --   }}
  --   let headerSnap := {
  --     beginPos := 0
  --     stx := Syntax.missing
  --     mpState := {}
  --     cmdState := cmdState
  --     interactiveDiags := ← cmdState.messages.msgs.mapM (Widget.msgToInteractiveDiagnostic m.text · hasWidgets)
  --     tacticCache := (← IO.mkRef {})
  --   }
  --   publishDiagnostics m headerSnap.diagnostics.toArray hOut
  --   return (headerSnap, paths)


  def compileHeader (m : DocumentMeta) (hOut : FS.Stream) (opts : Options) (hasWidgets : Bool)
      : IO (Syntax × Task (Except Error (Snapshot × SearchPath))) := do
    let gameDir := "../../../testgame"

    -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
    let out ← IO.Process.output
      { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
    if out.exitCode != 0 then
      throwServerError s!"Error while running Lake: {out.stderr}"

    -- Make the paths relative to the current directory
    let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
    let currentDir ← IO.currentDir
    let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

    -- Set the search path
    Lean.searchPathRef.set paths

    let gameName := `TestGame
    let env ← importModules [{ module := `Init : Import }, { module := gameName : Import }] {} 0
    -- return (env, paths)

    -- use empty header
    let (headerStx, headerParserState, msgLog) ← Parser.parseHeader
      {m.mkInputContext with
        input := ""
        fileMap := FileMap.ofString ""}
    (headerStx, ·) <$> EIO.asTask do
      let mut srcSearchPath : SearchPath := paths --← initSrcSearchPath (← getBuildDir)
      let headerEnv := env
      let mut headerEnv := headerEnv
      try
        if let some path := System.Uri.fileUriToPath? m.uri then
          headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
      catch _ => pure ()
      let cmdState := Elab.Command.mkState headerEnv {} opts
      let cmdState := { cmdState with infoState := {
        enabled := true
        trees := #[Elab.InfoTree.context ({
          env     := headerEnv
          fileMap := m.text
          ngen    := { namePrefix := `_worker }
        }) (Elab.InfoTree.node
            (Elab.Info.ofCommandInfo { elaborator := `header, stx := headerStx })
            (headerStx[1].getArgs.toList.map (fun importStx =>
              Elab.InfoTree.node (Elab.Info.ofCommandInfo {
                elaborator := `import
                stx := importStx
              }) #[].toPArray'
            )).toPArray'
        )].toPArray'
      }}
      let headerSnap := {
        beginPos := 0
        stx := headerStx
        mpState := {}
        cmdState := cmdState
        interactiveDiags := ← cmdState.messages.msgs.mapM (Widget.msgToInteractiveDiagnostic m.text · hasWidgets)
        tacticCache := (← IO.mkRef {})
      }
      publishDiagnostics m headerSnap.diagnostics.toArray hOut
      return (headerSnap, srcSearchPath)

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    let (headerStx, headerTask) ← compileHeader meta o opts (hasWidgets := clientHasWidgets)
    let cancelTk ← CancelToken.new
    let ctx :=
      { hIn  := i
        hOut := o
        hLog := e
        headerTask
        initParams
        clientHasWidgets
      }
    let cmdSnaps ← EIO.mapTask (t := headerTask) (match · with
      | Except.ok (s, _) => unfoldSnaps meta #[s] cancelTk ctx (startAfterMs := 0)
      | Except.error e   => throw (e : ElabTaskError))
    let doc : EditableDocument := { meta, cmdSnaps := AsyncList.delayed cmdSnaps, cancelTk }
    return (ctx,
    { doc             := doc
      initHeaderStx   := headerStx
      pendingRequests := RBMap.empty
      rpcSessions     := RBMap.empty
    })

end Initialization

section NotificationHandling

  def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc := (←get).doc
    let some newVersion ← pure docId.version?
      | throwServerError "Expected version number"
    if newVersion ≤ oldDoc.meta.version then
      -- TODO(WN): This happens on restart sometimes.
      IO.eprintln s!"Got outdated version number: {newVersion} ≤ {oldDoc.meta.version}"
    else if ¬ changes.isEmpty then
      let newDocText := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText⟩

end NotificationHandling

section MessageHandling

  def handleNotification (method : String) (params : Json) : WorkerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams handleRpcKeepAlive
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

end MessageHandling

section MainLoop
  partial def mainLoop : WorkerM Unit := do
    let ctx ← read
    let mut st ← get
    let msg ← ctx.hIn.readLspMessage
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : IO PendingRequestMap := do
      if (← hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        pure <| acc.erase id
      else pure acc
    let pendingRequests ← st.pendingRequests.foldM (fun acc id task => filterFinishedTasks acc id task) st.pendingRequests
    st := { st with pendingRequests }

    -- Opportunistically (i.e. when we wake up on messages) check if any RPC session has expired.
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
      let doc := st.doc
      doc.cancelTk.set
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) (opts : Options) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let doc := param.textDocument
  /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
    "\n", which should be enough to handle both LF and CRLF correctly.
    This is because LSP always refers to characters by (line, column),
    so if we get the line number correct it shouldn't matter that there
    is a CR there. -/
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap⟩
  let e := e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let (ctx, st) ← initializeWorker meta i o e initParams.param opts
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) mainLoop
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
    return (1 : UInt32)

def workerMain (opts : Options) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let exitCode ← initAndRunWorker i o e opts
    -- HACK: all `Task`s are currently "foreground", i.e. we join on them on main thread exit, but we definitely don't
    -- want to do that in the case of the worker processes, which can produce non-terminating tasks evaluating user code
    o.flush
    e.flush
    IO.Process.exit exitCode.toUInt8
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return (1 : UInt32)

end MyServer.FileWorker
