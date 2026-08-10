import Lean
import GameServer.RpcHandlers
import GameServer.SaveData
import GameServer.Tactic.LetIntros
import GameServer.Helpers.DeclSig

namespace GameServer

open Lean Meta Elab Command


-- TODO: use HashSet for allowed tactics?
/--
Find all tactics in syntax object that are forbidden according to a
set `allowed` of allowed tactics.
-/
partial def findForbiddenTactics
    (levelId : LevelId) (inventory : List String) (difficulty : Nat) (stx : Syntax) : CommandElabM Unit := do
  let levelInfo ← loadLevelData "." levelId.world levelId.level
  -- Parse the syntax object and look for tactics and declarations.
  match stx with
  | .missing => return ()
  | .node _info _kind args =>
    -- Go inside a node.
    for arg in args do
      findForbiddenTactics levelId inventory difficulty arg
  | .atom _ val =>
    -- Atoms might be tactic names or other keywords.
    -- Note: We whitelisted known keywords because we cannot
    -- distinguish keywords from tactic names.
    let allowed := GameServer.ALLOWED_KEYWORDS
    -- Ignore syntax elements that do not start with a letter or are listed above.
    if 0 < val.length ∧ val.toList[0]!.isAlpha ∧ not (allowed.contains val) then
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
          addMessageByDifficulty s!"The tactic '{val}' is not available in this game!"
      | some tac =>
        -- Tactic is introduced at some point in the game.
        if tac.disabled then
          -- Tactic is disabled in this level.
          addMessageByDifficulty s!"The tactic '{val}' is disabled in this level!"
        else if tac.locked then
          match inventory.find? (· == val) with
          | none =>
            -- Tactic is marked as locked and not in the inventory.
            addMessageByDifficulty s!"You have not unlocked the tactic '{val}' yet!"
          | some _ =>
            -- Tactic is in the inventory, allow it.
            pure ()
  | .ident _ _rawVal val _preresolved =>
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
        logErrorAt stx m!"Structural recursion: you can't use '{n}' to proof itself!"
      let theoremsAndDefs := levelInfo.lemmas ++ levelInfo.definitions
      match theoremsAndDefs.find? (·.name == n) with
      | none =>
        -- Theorem will never be introduced in this game
        addMessageByDifficulty s!"The theorem/definition '{n}' is not available in this game!"
      | some thm =>
        -- Theorem is introduced at some point in the game.
        if thm.disabled then
          -- Theorem is disabled in this level.
          addMessageByDifficulty s!"The theorem/definition '{n}' is disabled in this level!"
        else if thm.locked then
          match inventory.find? (· == n.toString) with
          | none =>
            -- Theorem is still locked.
            addMessageByDifficulty s!"You have not unlocked the theorem/definition '{n}' yet!"
          | some _ =>
            -- Theorem is in the inventory, allow it.
            pure ()

where addMessageByDifficulty (s : MessageData) :=
  -- Send nothing/warnings/errors depending on difficulty.
  if difficulty > 0 then
    logAt stx s (if difficulty > 1 then .error else .warning)
  else pure ()

/--
The scope of the level (i.e. the `open`s, the current namespace, the `set_option`s and the
`variable`s active at the `Statement` in the level file).

All position information is stripped from the syntax it contains: these positions point into
the level file and would otherwise be reported in the player's editor.
-/
def levelScope (level : GameLevel) : Elab.Command.Scope :=
  { level.scope with
    varDecls := level.scope.varDecls.map (⟨·.raw.rewriteBottomUp fun stx => stx.setInfo .none⟩)
    attrs :=  level.scope.attrs.map (⟨·.raw.rewriteBottomUp fun stx => stx.setInfo .none⟩)
  }

/-- Activate the scoped declarations (`scoped notation`, `scoped instance`, `scoped attribute`,
…) of all namespaces that are open in `scope`. -/
def activateScopedInScope (scope : Elab.Command.Scope) : CommandElabM Unit := do
  for od in scope.openDecls do
    let .simple ns _ := od
      | pure ()
    activateScoped ns
  -- entering `namespace A.B` activates the scoped declarations of both `A` and `A.B`
  let mut ns := Name.anonymous
  for component in scope.currNamespace.components do
    ns := ns ++ component
    activateScoped ns

/--
Set the scope of the level (`open`s, current namespace, `set_option`s, `variable`s) in the
command state.

This needs to be a command of its own, placed *before* `Runner`: Lean parses each command with
the scope the command state has *before* that command is parsed. Everything that influences
parsing – most notably `scoped notation` such as `𝓝` from `open Topology` – is therefore only
available in the player's proof if the corresponding `open` has already been processed by an
earlier command. The `withScope` inside `Runner` only affects elaboration and comes too late for
the parser, which has already turned `𝓝 x` into an application of the unknown identifier `𝓝`.
-/
elab "LevelScope" gameId:str worldId:str levelId:num : command => do
  let levelId := {game := gameId.getString, world := worldId.getString, level := levelId.getNat}

  let some level ← getLevel? levelId
    | logError m!"Level not found: {levelId}"

  let scope := levelScope level
  -- Only apply what the *parser* of the following command needs, i.e. the namespace and the
  -- `open`s. Everything else (options, `variable`s, …) is applied by `Runner` itself.
  --
  -- In particular the level's options must not be copied here: they are recorded while the game
  -- is built with `lake build` and hence contain `internal.cmdlineSnapshots := true`. Applied to
  -- the scope of the file, that makes the language server drop the info tree of the `Runner`
  -- command, and the game can then no longer display any goals or hints.
  modifyScope fun fileScope => { fileScope with
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls }
  activateScopedInScope scope

-- TODO(Alex): Use config parser?
-- TODO(Alex): Ensure Runner is the last command in the file
/-- Run a game level -/
elab "Runner" gameId:str worldId:str levelId:num
 "(" &"difficulty" ":=" difficulty:num ")"
 "(" &"inventory" ":=" "[" inventory:str,* "]" ")" ":=" byStx:&"by"
 tacticStx:tacticSeq ? : command => do

  let levelId := {game := gameId.getString, world := worldId.getString, level := levelId.getNat}
  let difficulty := difficulty.getNat
  let inventory := inventory.getElems.map (·.getString) |>.toList

  let some level ← getLevel? levelId
    | logError m!"Level not found: {levelId}"

  -- use open namespaces and options as in the level file.
  -- Note: this only affects elaboration; for anything that affects parsing (i.e. scoped
  -- notation) the `LevelScope` command above has to be run as a separate, earlier command.
  let scope := levelScope level
  Elab.Command.withScope (fun _ => scope) do
    activateScopedInScope scope

    -- Position before first tactic and any prepended whitespace
    let startPos := byStx.getTailInfo.getRange?.getD (Lean.Syntax.Range.mk 0 0) |>.stop

    -- Position behind the last tactic
    let endPos := (tacticStx.map TSyntax.raw).getD byStx
      |>.getTailInfo |>.getRangeWithTrailing? |>.getD (Lean.Syntax.Range.mk 0 0) |>.stop
    -- Adjust endPos to be one character earlier (probably the end of file character?)
    let endPos := ⟨endPos.byteIdx-1⟩

    let tacticStx : Array (TSyntax `tactic) ← (do
      match tacticStx with
      | some ⟨tacticStx⟩ =>
        -- Check for forbidden tactics
        findForbiddenTactics levelId inventory difficulty tacticStx
        return tacticStx.getArgs.map (⟨.⟩)
      | none => -- empty tactic sequence
        -- Insert invisible `skip` command to make sure we always display the initial goal
        let skip := Syntax.node (.original default startPos default endPos)
          ``Lean.Parser.Tactic.skip #[]
        return #[⟨skip⟩]
    )

    -- Insert final `done` command to display unsolved goal error in the end
    let done := Syntax.node (.synthetic endPos endPos) ``Lean.Parser.Tactic.done #[]
    let tacticStx := tacticStx ++ #[⟨done⟩]

    let tacticStx := ← `(Lean.Parser.Tactic.tacticSeq| $[$(tacticStx)]*)

    let goal := ⟨level.goal.raw.rewriteBottomUp fun stx => stx.setInfo .none⟩

    let isProp := level.isProp
    let optDeclSig := declSig.toOptDeclSig goal


    -- Run the proof
    let thmStatement ← match isProp with
    | true => `(command| theorem the_theorem $(goal) := by {let_intros; $(⟨level.preamble⟩); $(⟨tacticStx⟩)} )
    | false => `(command| def the_theorem $(optDeclSig) := by {let_intros; $(⟨level.preamble⟩); $(⟨tacticStx⟩)} )

    elabCommand thmStatement
