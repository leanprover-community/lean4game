import GameServer.EnvExtensions

open Lean Meta Elab Command

set_option autoImplicit false

/-! # Game metadata -/

/-- Switch to the specified `Game` (and create it if non-existent). Example: `Game "NNG"` -/
elab "Game" n:str : command => do
  let name := n.getString
  setCurGameId name
  if (← getGame? name).isNone then
    insertGame name {name}

/-- Create a new world in the active game. Example: `World "Addition"` -/
elab "World" n:str : command => do
  let name := n.getString
  setCurWorldId name
  if ¬ (← getCurGame).worlds.nodes.contains name then
    addWorld {name}

/-- Define the current level number. Levels inside a world must be
numbered consecutive starting with `1`. Example: `Level 1` -/
elab "Level" level:num : command => do
  let level := level.getNat
  setCurLevelIdx level
  addLevel {index := level}

/-- Define the title of the current game/world/level. -/
elab "Title" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with title := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with title := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with title := t.getString}

/-- Define the introduction of the current game/world/level. -/
elab "Introduction" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with introduction := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with introduction := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with introduction := t.getString}

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := t.getString}


/-! # Inventory

The inventory contains docs for tactics, lemmas, and definitions. These are all locked
in the first level and get enabled during the game.
-/

/-! ## Doc entries -/

/-- Checks if `inventoryTemplateExt` contains an entry with `(type, name)` and yields
a warning otherwise. If `template` is provided, it will add such an entry instead of yielding a
warning. -/
def checkInventoryDoc (type : InventoryType) (name : Ident)
    (template : Option String := none) : CommandElabM Unit := do
  -- note: `name` is an `Ident` (instead of `Name`) for the log messages.
  let env ← getEnv
  let n := name.getId
  -- Find a key with matching `(type, name)`.
  match (inventoryTemplateExt.getState env).findIdx?
    (fun x => x.name == n && x.type == type) with
  -- Nothing to do if the entry exists
  | some _ => pure ()
  | none =>
    match template with
    -- Warn about missing documentation
    | none =>
      -- We just add a dummy entry
      modifyEnv (inventoryTemplateExt.addEntry · {
        type := type
        name := name.getId
        category := if type == .Lemma then s!"{n.getPrefix}" else "" })
      logWarningAt name (m!"Missing {type} Documentation: {name}\nAdd `{type}Doc {name}` " ++
        m!"somewhere above this statement.")
    -- Add the default documentation
    | some s =>
      modifyEnv (inventoryTemplateExt.addEntry · {
        type := type
        name := name.getId
        category := if type == .Lemma then s!"{n.getPrefix}" else ""
        content := s })
      logInfoAt name (m!"Missing {type} Documentation: {name}, used provided default (e.g. " ++
      m!"statement description) instead. If you want to write your own description, add " ++
      m!"`{type}Doc {name}` somewhere above this statement.")

/-- Documentation entry of a tactic. Example:

```
TacticDoc rw "`rw` stands for rewrite, etc. "
```

* The identifier is the tactics name. Some need to be escaped like `«have»`.
* The description is a string supporting Markdown.
 -/
elab "TacticDoc" name:ident content:str : command =>
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Tactic
    name := name.getId
    displayName := name.getId.toString
    content := content.getString })

/-- Documentation entry of a lemma. Example:

```
LemmaDoc Nat.succ_pos as "succ_pos" in "Nat" "says `0 < n.succ`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Lemma`.
  It is preferably the true name of the lemma. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The identifier after `in` is the category to group lemmas by (in the Inventory).
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requries
The lemma/definition to have the same fully qualified name as in mathlib.
 -/
elab "LemmaDoc" name:ident "as" displayName:str "in" category:str content:str : command =>
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Lemma
    name := name.getId
    category := category.getString
    displayName := displayName.getString
    content := content.getString })
-- TODO: Catch the following behaviour.
-- 1. if `LemmaDoc` appears in the same file as `Statement`, it will silently use
-- it but display the info that it wasn't found in `Statement`
-- 2. if it appears in a later file, however, it will silently not do anything and keep
-- the first one.


/-- Documentation entry of a definition. Example:

```
DefinitionDoc Function.Bijective as "Bijective" "defined as `Injective f ∧ Surjective`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Definition`.
  It is preferably the true name of the definition. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requries
The lemma/definition to have the same fully qualified name as in mathlib.
 -/
elab "DefinitionDoc" name:ident "as" displayName:str template:str : command =>
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Definition
    name := name.getId,
    displayName := displayName.getString,
    content := template.getString })

/-! ## Add inventory items -/

-- namespace Lean.PrettyPrinter
-- def ppSignature' (c : Name) : MetaM String := do
--   let decl ← getConstInfo c
--   let e := .const c (decl.levelParams.map mkLevelParam)
--   let (stx, _) ← delabCore e (delab := Delaborator.delabConstWithSignature)
--   let f ← ppTerm stx
--   return toString f
-- end Lean.PrettyPrinter

def getStatement (name : Name) : CommandElabM MessageData := do
  -- let c := name.getId

  let decl ← getConstInfo name
  -- -- TODO: How to go between CommandElabM and MetaM

  -- addCompletionInfo <| .id name c (danglingDot := false) {} none
  return ← addMessageContextPartial (.ofPPFormat { pp := fun
    | some ctx => ctx.runMetaM <| ppExpr decl.type
    -- PrettyPrinter.ppSignature' c
    -- PrettyPrinter.ppSignature c
    | none     => return "that's a bug." })

-- Note: We use `String` because we can't send `MessageData` as json, but
-- `MessageData` might be better for interactive highlighting.
/-- Get a string of the form `my_lemma (n : ℕ) : n + n = 2 * n`. -/
def getStatementString (name : Name) : CommandElabM String := do
  try
    return ← (← getStatement name).toString
  catch
  | _ => throwError m!"Could not find {name} in context."
  -- TODO: I think it would be nicer to unresolve Namespaces as much as possible.

/-- Declare tactics that are introduced by this level. -/
elab "NewTactic" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Tactic name -- TODO: Add (template := "[docstring]")
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with new := args.map (·.getId)}}

/-- Declare lemmas that are introduced by this level. -/
elab "NewLemma" args:ident* : command => do
  for name in ↑args do
    checkInventoryDoc .Lemma name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with new := args.map (·.getId)}}

/-- Declare definitions that are introduced by this level. -/
elab "NewDefinition" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Definition name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with new := args.map (·.getId)}}

/-- Declare tactics that are temporarily disabled in this level.
This is ignored if `OnlyTactic` is set. -/
elab "DisabledTactic" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with disabled := args.map (·.getId)}}

/-- Declare lemmas that are temporarily disabled in this level.
This is ignored if `OnlyLemma` is set. -/
elab "DisabledLemma" args:ident* : command => do
  for name in ↑args  do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with disabled := args.map (·.getId)}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinition" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with disabled := args.map (·.getId)}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactic" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with only := args.map (·.getId)}}

/-- Temporarily disable all lemmas except the ones declared here -/
elab "OnlyLemma" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with only := args.map (·.getId)}}

/-- Temporarily disable all definitions except the ones declared here.
This is ignored if `OnlyDefinition` is set. -/
elab "OnlyDefinition" args:ident* : command => do
  for name in ↑args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with only := args.map (·.getId)}}

/-- Define which tab of Lemmas is opened by default. Usage: `LemmaTab "Nat"`.
If omitted, the current tab will remain open. -/
elab "LemmaTab"  category:str : command =>
  modifyCurLevel fun level => pure {level with lemmaTab := category.getString}

/-! # Exercise Statement -/

/-- A `attr := ...` option for `Statement`. Add attributes to the defined theorem. -/
syntax statementAttr := "(" &"attr" ":=" Parser.Term.attrInstance,* ")"
-- TODO

-- TODO: Reuse the following code for checking available tactics in user code:
structure UsedInventory where
(tactics : HashSet Name := {})
(definitions : HashSet Name := {})
(lemmas : HashSet Name := {})

partial def collectUsedInventory (stx : Syntax) (acc : UsedInventory := {}) : CommandElabM UsedInventory := do
  match stx with
  | .missing => return acc
  | .node info kind args =>
    if kind == `tacticHint__ || kind == `tacticBranch_ then return acc
    return ← args.foldlM (fun acc arg => collectUsedInventory arg acc) acc
  | .atom info val =>
    -- ignore syntax elements that do not start with a letter
    -- and ignore some standard keywords
    let allowed := ["with", "fun", "at", "only", "by"]
    if 0 < val.length ∧ val.data[0]!.isAlpha ∧ not (allowed.contains val) then
      let val := val.dropRightWhile (fun c => c == '!' || c == '?') -- treat `simp?` and `simp!` like `simp`
      return {acc with tactics := acc.tactics.insert val}
    else
      return acc
  | .ident info rawVal val preresolved =>
      let ns ←
        try resolveGlobalConst (mkIdent val)
        catch | _ => pure [] -- catch "unknown constant" error
      return ← ns.foldlM (fun acc n => do
        if let some (.thmInfo ..) := (← getEnv).find? n then
          return {acc with lemmas := acc.lemmas.insertMany ns}
        else
          return {acc with definitions := acc.definitions.insertMany ns}
      ) acc

/-- Define the statement of the current level. -/
elab "Statement" statementName:ident ? descr:str ? sig:declSig val:declVal : command => do
  let lvlIdx ← getCurLevelIdx

  let descr := match descr with
    | none => none
    | some s => s.getString

  -- Save the messages before evaluation of the proof.
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })

  -- The default name of the statement is `[Game].[World].level[no.]`, e.g. `NNG.Addition.level1`
  -- However, this should not be used when designing the game.
  let defaultDeclName : Ident := mkIdent <| (← getCurGame).name ++ (← getCurWorld).name ++
    ("level" ++ toString lvlIdx : String)

  -- Collect all used tactics/lemmas in the sample proof:
  let usedInventory ← match val with
  | `(Parser.Command.declVal| := $proof:term) => do
    collectUsedInventory proof
  | _ => throwError "expected `:=`"

  -- Add theorem to context.
  match statementName with
  | some name =>
    let env ← getEnv

    let fullName := (← getCurrNamespace) ++ name.getId

    if env.contains fullName then
      let origType := (env.constants.map₁.find! fullName).type
      -- TODO: Check if `origType` agrees with `sig` and output `logInfo` instead of `logWarning`
      -- in that case.
      logWarningAt name (m!"Environment already contains {fullName}! Only the existing " ++
      m!"statement will be available in later levels:\n\n{origType}")
      let thmStatement ← `(theorem $defaultDeclName $sig $val)
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Lemma name (template := descr)

    else
      let thmStatement ← `( theorem $name $sig $val)
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Lemma name (template := descr)

  | none =>
    let thmStatement ← `(theorem $defaultDeclName $sig $val)
    elabCommand thmStatement

  let msgs := (← get).messages

  let mut hints := #[]
  let mut nonHintMsgs := #[]
  for msg in msgs.msgs do
    -- Look for messages produced by the `Hint` tactic. They are used to pass information about the
    -- intermediate goal state
    if let MessageData.withNamingContext _ $ MessageData.withContext ctx $
        .tagged `Hint $
        .nest strict $
        .nest hidden $
        .compose (.ofGoal text) (.ofGoal goal) := msg.data then
      let hint ← liftTermElabM $ withMCtx ctx.mctx $ withLCtx ctx.lctx #[] $ withEnv ctx.env do
        return {
          goal := ← abstractCtx goal
          text := ← instantiateMVars (mkMVar text)
          strict := strict == 1
          hidden := hidden == 1
        }
      hints := hints.push hint
    else
      nonHintMsgs := nonHintMsgs.push msg

  -- restore saved messages and non-hint messages
  modify fun st => { st with
    messages := initMsgs ++ ⟨nonHintMsgs.toPArray'⟩
  }

  let scope ← getScope
  let env ← getEnv

  -- TODO: Is this desired or would it be better to get `elabCommand` above to ignore
  -- the namespace?
  let currNamespace ← getCurrNamespace

  let st ← match statementName with
  | some name => getStatementString <| currNamespace ++ name.getId
  | none =>  getStatementString <| currNamespace ++ (defaultDeclName).getId

  let head := match statementName with
  | some name => Format.join ["theorem ", (currNamespace ++ name.getId).toString]
  | none => "example"

  modifyCurLevel fun level => pure { level with
    module := env.header.mainModule
    goal := sig,
    scope := scope,
    descrText := descr
    statementName := match statementName with
    | none => default
    | some name => currNamespace ++ name.getId
    descrFormat := (Format.join [head, " ", st, " := by"]).pretty 10
    hints := hints
    tactics := {level.tactics with used := usedInventory.tactics.toArray}
    definitions := {level.definitions with used := usedInventory.definitions.toArray}
    lemmas := {level.lemmas with used := usedInventory.lemmas.toArray} }

/-! # Hints -/

syntax hintArg := atomic(" (" (&"strict" <|> &"hidden") " := " withoutPosition(term) ")")

/-- Remove any spaces at the beginning of a new line -/
partial def removeIndentation (s : String) : String :=
  let rec loop (i : String.Pos) (acc : String) (removeSpaces := false) : String :=
    let c := s.get i
    let i := s.next i
    if s.atEnd i then
      acc.push c
    else if removeSpaces && c == ' ' then
      loop i acc (removeSpaces := true)
    else if c == '\n' then
      loop i (acc.push c) (removeSpaces := true)
    else
      loop i (acc.push c)
  loop ⟨0⟩ ""

/-- A tactic that can be used inside `Statement`s to indicate in which proof states players should
see hints. The tactic does not affect the goal state.
-/
elab "Hint" args:hintArg* msg:interpolatedStr(term) : tactic => do
  let mut strict := false
  let mut hidden := false

  -- remove spaces at the beginngng of new lines
  let msg := TSyntax.mk $ msg.raw.setArgs $ ← msg.raw.getArgs.mapM fun m => do
    match m with
    | Syntax.node info k args =>
      if k == interpolatedStrLitKind && args.size == 1 then
        match args.get! 0 with
        | (Syntax.atom info' val) =>
          let val := removeIndentation val
          return Syntax.node info k #[Syntax.atom info' val]
        | _ => return m
      else
        return m
    | _ => return m

  for arg in args do
    match arg with
    | `(hintArg| (strict := true)) => strict := true
    | `(hintArg| (strict := false)) => strict := false
    | `(hintArg| (hidden := true)) => hidden := true
    | `(hintArg| (hidden := false)) => hidden := false
    | _ => throwUnsupportedSyntax

  let goal ← Tactic.getMainGoal
  goal.withContext do
    -- We construct an expression that can produce the hint text. The difficulty is that we
    -- want the text to possibly contain quotation of the local variables which might have been
    -- named differently by the player.
    let varsName := `vars
    let text ← withLocalDeclD varsName (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr)) fun vars => do
      let mut text ← `(m! $msg)
      let goalDecl ← goal.getDecl
      let decls := goalDecl.lctx.decls.toArray.filterMap id
      for i in [:decls.size] do
        text ← `(let $(mkIdent decls[i]!.userName) := $(mkIdent varsName)[$(quote i)]!; $text)
      return ← mkLambdaFVars #[vars] $ ← Term.elabTermAndSynthesize text none
    let textmvar ← mkFreshExprMVar none
    guard $ ← isDefEq textmvar text -- Store the text in a mvar.
    -- The information about the hint is logged as a message using `logInfo` to transfer it to the
    -- `Statement` command:
    logInfo $
      .tagged `Hint $
      .nest (if strict then 1 else 0) $
      .nest (if hidden then 1 else 0) $
      .compose (.ofGoal textmvar.mvarId!) (.ofGoal goal)

/-- This tactic allows us to execute an alternative sequence of tactics, but without affecting the
proof state. We use it to define Hints for alternative proof methods or dead ends. -/
elab "Branch" t:tacticSeq : tactic => do
  let b ← saveState
  Tactic.evalTactic t

  -- Show an info whether the branch proofs all remaining goals.
  let gs ← Tactic.getUnsolvedGoals
  if gs.isEmpty then
    logInfo "This branch finishes the proof."
  else
    logInfo "This branch leaves open goals."

  let msgs ← Core.getMessageLog
  b.restore
  Core.setMessageLog msgs



/-- The tactic block inside `Template` will be copied into the users editor.
Use `Hole` inside the template for a part of the proof that should be replaced
with `sorry`. -/
elab "Template" t:tacticSeq : tactic => do
  --let b ← saveState
  Tactic.evalTactic t

  -- -- Not correct
  -- let gs ← Tactic.getUnsolvedGoals
  -- if ¬ gs.isEmpty then
  --   logWarning "To work as intended, `Template` should contain the entire proof"


  -- -- Show an info whether the branch proofs all remaining goals.
  -- let gs ← Tactic.getUnsolvedGoals
  -- if gs.isEmpty then
  --   logInfo "This branch finishes the proof."
  -- else
  --   logInfo "This branch leaves open goals."

  -- let msgs ← Core.getMessageLog
  -- b.restore
  -- Core.setMessageLog msgs


/-- A hole inside a template proof that will be replaced by `sorry`. -/
elab "Hole" t:tacticSeq : tactic => do
  Tactic.evalTactic t


-- TODO: Notes for testing if a declaration has the simp attribute

-- -- Test: From zulip
-- section test

-- open Lean Meta Elab Command Tactic Simp

-- def Lean.Meta.SimpTheorems.hasAttribute (d : SimpTheorems) (decl : Name) :=
--   d.isLemma (.decl decl) || d.isDeclToUnfold decl

-- def isInSimpset (simpAttr decl: Name) : CoreM Bool := do
--   let .some simpDecl ←getSimpExtension? simpAttr | return false
--   return (← simpDecl.getTheorems).hasAttribute decl

-- end test

/-! # Make Game -/

def GameLevel.getInventory (level : GameLevel) : InventoryType → InventoryInfo
| .Tactic => level.tactics
| .Definition => level.definitions
| .Lemma => level.lemmas

def GameLevel.setComputedInventory (level : GameLevel) :
    InventoryType → Array InventoryTile → GameLevel
| .Tactic, v =>     {level with tactics     := {level.tactics     with tiles := v}}
| .Definition, v => {level with definitions := {level.definitions with tiles := v}}
| .Lemma, v =>      {level with lemmas      := {level.lemmas      with tiles := v}}

/-- Copied from `Mathlib.Tactic.HelpCmd`.

Gets the initial string token in a parser description. For example, for a declaration like
`syntax "bla" "baz" term : tactic`, it returns `some "bla"`. Returns `none` for syntax declarations
that don't start with a string constant. -/
partial def getHeadTk (e : Expr) : Option String :=
  match (Expr.withApp e λ e a => (e.constName?.getD Name.anonymous, a)) with
  | (``ParserDescr.node, #[_, _, p]) => getHeadTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "withPosition")), p]) => getHeadTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "atomic")), p]) => getHeadTk p
  | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, _]) => getHeadTk p
  | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _]) => some tk
  | (``ParserDescr.symbol, #[.lit (.strVal tk)]) => some tk
  | (``Parser.withAntiquot, #[_, p]) => getHeadTk p
  | (``Parser.leadingNode, #[_, _, p]) => getHeadTk p
  | (``HAndThen.hAndThen, #[_, _, _, _, p, _]) => getHeadTk p
  | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) => some tk
  | (``Parser.symbol, #[.lit (.strVal tk)]) => some tk
  | _ => none

/-- Modified from `#help` in `Mathlib.Tactic.HelpCmd` -/
def getTacticDocstring (env : Environment) (name: Name) : CommandElabM (Option String) := do
  let name := name.toString (escape := false)
  let mut decls : Lean.RBMap String (Array SyntaxNodeKind) compare := {}

  let catName : Name := `tactic
  let catStx : Ident := mkIdent catName -- TODO
  let some cat := (Parser.parserExtension.getState env).categories.find? catName
    | throwErrorAt catStx "{catStx} is not a syntax category"
  liftTermElabM <| Term.addCategoryInfo catStx catName
  for (k, _) in cat.kinds do
    let mut used := false
    if let some tk := do getHeadTk (← (← env.find? k).value?) then
      let tk := tk.trim
      if name ≠ tk then -- was `!name.isPrefixOf tk`
        continue
      used := true
      decls := decls.insert tk ((decls.findD tk #[]).push k)
  for (_name, ks) in decls do
    for k in ks do
      if let some doc ← findDocString? env k then
        return doc

  logWarning <| m!"Could not find a docstring for this tactic, consider adding one " ++
    m!"using `TacticDoc {name} \"some doc\"`"
  return none

/-- Retrieve the docstring associated to an inventory item. For Tactics, this
is not guaranteed to work. -/
def getDocstring (env : Environment) (name : Name) (type : InventoryType) :
    CommandElabM (Option String) :=
  match type with
  -- for tactics it's a lookup following mathlib's `#help`. not guaranteed to be the correct one.
  | .Tactic => getTacticDocstring env name
  | .Lemma => findDocString? env name
  -- TODO: for definitions not implemented yet, does it work?
  | .Definition => findDocString? env name


partial def removeTransitiveAux (id : Name) (arrows : HashMap Name (HashSet Name))
      (newArrows : HashMap Name (HashSet Name)) (decendants : HashMap Name (HashSet Name)) :
    HashMap Name (HashSet Name) × HashMap Name (HashSet Name) := Id.run do
  match (newArrows.find? id, decendants.find? id) with
  | (some _, some _) => return (newArrows, decendants)
  | _ =>
    let mut newArr := newArrows
    let mut desc := decendants
    desc := desc.insert id {} -- mark as worked in case of loops
    newArr := newArr.insert id {} -- mark as worked in case of loops
    let children := arrows.find! id
    let mut trimmedChildren := children
    let mut theseDescs := children
    for child in children do
      (newArr, desc) := removeTransitiveAux child arrows newArr desc
      let childDescs := desc.find! child
      theseDescs := theseDescs.insertMany childDescs
      for d in childDescs do
        trimmedChildren := trimmedChildren.erase d
    desc := desc.insert id theseDescs
    newArr := newArr.insert id trimmedChildren
    return (newArr, desc)

def removeTransitive (arrows : HashMap Name (HashSet Name)) : CommandElabM (HashMap Name (HashSet Name)) := do
  let mut newArr := {}
  let mut desc := {}
  for id in arrows.toArray.map Prod.fst do
    (newArr, desc) := removeTransitiveAux id arrows newArr desc
    if (desc.find! id).contains id then logWarning m!"Loop at {id}"
  return newArr


/-- Check if graph contains loops -/
partial def findLoops (arrows : HashMap Name (HashSet Name)) (visited0 : HashSet Name := {}): List Name := Id.run do
  let mut visited : HashSet Name := visited0
  let all : Array Name := arrows.toArray.map (·.1)

  -- find some node that we haven't visited
  let some x := all.find? fun x => ¬ visited.contains x
    | return [] -- We have visted all nodes and found no loops
  visited := visited.insert x

  match visitSuccessors x x visited with -- visit all recursive successors of x
  | .inl visited' => visited := visited'
  | .inr l => return l -- a loop has been found

  findLoops arrows visited -- continue looking for unvisited nodes
where
  visitSuccessors (x : Name) (x0 : Name) (visited0 : HashSet Name) : Sum (HashSet Name) (List Name) := Id.run do
    let mut visited : HashSet Name := visited0

    let directSuccessors := arrows.findD x {}
    for y in directSuccessors do
      if y == x0 then
        return .inr [x] -- loop found
      if visited.contains y then
        continue -- no loop possible here because the visited nodes do not lead to x0
      visited := visited.insert y
      match visitSuccessors y x0 visited with
      | .inl visited' => visited := visited'
      | .inr l => return .inr (x :: l)

    return .inl visited

/-- Build the game. This command will precompute various things about the game, such as which
tactics are available in each level etc. -/
elab "MakeGame" : command => do
  let game ← getCurGame

  let env ← getEnv

  -- Now create The doc entries from the templates
  for item in inventoryTemplateExt.getState env do
    let name := item.name

    let docstring ← getDocstring env name item.type
    let content : String := match item.content with
    | "" =>
      -- If documentation is missing, try using the docstring instead.
      match docstring with
      | some ds => s!"*(lean docstring)*\\\n{ds}" -- TODO `\n` does not work in markdown
      | none => "(missing)"
    | template =>
      -- TODO: Process content template.
      -- TODO: Add information about inventory items
      template.replace "[[mathlib_doc]]"
        s!"[mathlib doc](https://leanprover-community.github.io/mathlib4_docs/find/?pattern={name}#doc)"

    match item.type with
    | .Lemma =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
        -- Add the lemma statement to the doc
        statement := (← getStatementString name)
      })
    | _ =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
      })


  -- Which items are used/new in which world?
  let mut usedItemsInWorld : HashMap Name (HashSet Name) := {}
  let mut newItemsInWorld : HashMap Name (HashSet Name) := {}
  for (worldId, world) in game.worlds.nodes.toArray do
    let mut usedItems : HashSet Name := {}
    let mut newItems : HashSet Name := {}
    for inventoryType in #[.Tactic, .Definition, .Lemma] do
      for (levelId, level) in world.levels.toArray do
          usedItems := usedItems.insertMany (level.getInventory inventoryType).used
          newItems := newItems.insertMany (level.getInventory inventoryType).new
    usedItemsInWorld := usedItemsInWorld.insert worldId usedItems
    newItemsInWorld := newItemsInWorld.insert worldId newItems

  let mut worldsWithNewItem : HashMap Name (HashSet Name) := {}
  for (worldId, world) in game.worlds.nodes.toArray do
    for newItem in newItemsInWorld.find! worldId do
      worldsWithNewItem := worldsWithNewItem.insert newItem $
        (worldsWithNewItem.findD newItem {}).insert worldId

  -- which world depends on which world?
  let mut worldDependsOnWorlds : HashMap Name (HashSet Name) := {}
  let mut dependencyReason : HashMap (Name × Name) Name := {}
  for (dependentWorldId, dependentWorld) in game.worlds.nodes.toArray do
    let mut dependsOnWorlds : HashSet Name := {}
    for usedItem in usedItemsInWorld.find! dependentWorldId do
      match worldsWithNewItem.find? usedItem with
      | some worldIds =>
        if !worldIds.contains dependentWorldId then
          dependsOnWorlds := dependsOnWorlds.insertMany worldIds
          for worldId in worldIds do
            dependencyReason := dependencyReason.insert (dependentWorldId, worldId) usedItem
      | none => logWarning m!"No world introducing {usedItem}, but required by {dependentWorldId}"
    worldDependsOnWorlds := worldDependsOnWorlds.insert dependentWorldId dependsOnWorlds

  let loop := findLoops worldDependsOnWorlds
  if loop != [] then
    logError m!"Loop: Dependency graph has a loop: {loop}"
    for i in [:loop.length] do
      let w1 := loop[i]!
      let w2 := loop[if i == loop.length - 1 then 0 else i + 1]!
      let item := dependencyReason.find! (w1, w2)
      logError m!"{w1} depends on {w2} because of {item}"
  else
    worldDependsOnWorlds ← removeTransitive worldDependsOnWorlds
    for (dependentWorldId, worldIds) in worldDependsOnWorlds.toArray do
      modifyCurGame fun game =>
        pure {game with worlds := {game.worlds with
          edges := game.worlds.edges.append (worldIds.toArray.map fun wid => (wid, dependentWorldId))}}

  -- Compute which inventory items are available in which level:
  for inventoryType in #[.Tactic, .Definition, .Lemma] do

    -- Which items are introduced in which world?
    let mut newItemsInWorld' : HashMap Name (HashSet Name) := {}
    let mut lemmaStatements : HashMap (Name × Nat) Name := {}
    let mut allItems : HashSet Name := {}
    for (worldId, world) in game.worlds.nodes.toArray do
      let mut newItems : HashSet Name := {}
      for (levelId, level) in world.levels.toArray do
        let newLemmas := (level.getInventory inventoryType).new
        newItems := newItems.insertMany newLemmas
        allItems := allItems.insertMany newLemmas
        if inventoryType == .Lemma then
          -- For levels `2, 3, …` we check if the previous level was named
          -- in which case we add it as available lemma.
          match levelId with
          | 0 => pure ()
          | 1 => pure () -- level ids start with 1, so we need to skip 1, too.
          | i₀ + 1 =>
            -- add named statement from previous level to the available lemmas.
            match (world.levels.find! (i₀)).statementName with
            | .anonymous => pure ()
            | .num _ _ => panic "Did not expect to get a numerical statement name!"
            | .str pre s =>
              let name := Name.str pre s
              newItems := newItems.insert name
              allItems := allItems.insert name
              lemmaStatements := lemmaStatements.insert (worldId, levelId) name
      if inventoryType == .Lemma then
        -- if named, add the lemma from the last level of the world to the inventory
        let i₀ := world.levels.size
        match (world.levels.find! (i₀)).statementName with
        | .anonymous => pure ()
        | .num _ _ => panic "Did not expect to get a numerical statement name!"
        | .str pre s =>
          let name := Name.str pre s
          newItems := newItems.insert name
          allItems := allItems.insert name
      newItemsInWorld' := newItemsInWorld'.insert worldId newItems

    -- Basic inventory item availability: all locked.
    let Availability₀ : HashMap Name InventoryTile :=
      HashMap.ofList $
        ← allItems.toList.mapM fun item => do
          let data := (← getInventoryItem? item inventoryType).get!
          -- TODO: BUG, panic at `get!` in vscode
          return (item, {
            name := item
            displayName := data.displayName
            category := data.category })

    -- Availability after a given world
    let mut itemsInWorld : HashMap Name (HashMap Name InventoryTile) := {}
    for (worldId, _) in game.worlds.nodes.toArray do
      -- Unlock all items from previous worlds
      let mut items := Availability₀
      let predecessors := worldDependsOnWorlds.find! worldId
      for predWorldId in predecessors do
        for item in newItemsInWorld'.find! predWorldId do
          let data := (← getInventoryItem? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false }
      itemsInWorld := itemsInWorld.insert worldId items

    for (worldId, world) in game.worlds.nodes.toArray do
      let mut items := itemsInWorld.find! worldId

      let levels := world.levels.toArray.insertionSort fun a b => a.1 < b.1

      for (levelId, level) in levels do
        let levelInfo := level.getInventory inventoryType

        -- unlock items that are unlocked in this level
        for item in levelInfo.new do
          let data := (← getInventoryItem? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false }

        -- add the exercise statement from the previous level
        -- if it was named
        if inventoryType == .Lemma then
          match lemmaStatements.find? (worldId, levelId) with
          | none => pure ()
          | some name =>
            let data := (← getInventoryItem? name inventoryType).get!
            items := items.insert name {
              name := name
              displayName := data.displayName
              category := data.category
              locked := false }

        -- add marks for `disabled` and `new` lemmas here, so that they only apply to
        -- the current level.
        let itemsArray := items.toArray
          |>.insertionSort (fun a b => a.1.toString < b.1.toString)
          |>.map (·.2)
          |>.map (fun item => { item with
            disabled := if levelInfo.only.size == 0 then
                levelInfo.disabled.contains item.name
              else
                not (levelInfo.only.contains item.name)
            new := levelInfo.new.contains item.name
            })

        modifyLevel ⟨← getCurGameId, worldId, levelId⟩ fun level => do
          return level.setComputedInventory inventoryType itemsArray


/-! # Debugging tools -/

-- /-- Print current game for debugging purposes. -/
-- elab "PrintCurGame" : command => do
--   logInfo (toJson (← getCurGame))

/-- Print current level for debugging purposes. -/
elab "PrintCurLevel" : command => do
  logInfo (repr (← getCurLevel))

/-- Print levels for debugging purposes. -/
elab "PrintLevels" : command => do
  logInfo $ repr $ (← getCurWorld).levels.toArray
