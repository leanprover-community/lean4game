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

  -- use open namespaces and options as in the level file
  let scope := { level.scope with
    varDecls := level.scope.varDecls.map (⟨·.raw.rewriteBottomUp fun stx => stx.setInfo .none⟩)
    attrs :=  level.scope.attrs.map (⟨·.raw.rewriteBottomUp fun stx => stx.setInfo .none⟩)
  }
  Elab.Command.withScope (fun _ => scope) do
    for od in scope.openDecls do
      let .simple ns _ := od
        | pure ()
      activateScoped ns
    activateScoped scope.currNamespace

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
