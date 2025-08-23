import GameServer.Tactic.Branch
import GameServer.Tactic.Hint

namespace GameServer

open Lean Elab Command

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

/-! ## Doc entries -/

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

  logWarning <| m!"Could not find a docstring for tactic {name}, consider adding one " ++
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

/-- Checks if `inventoryTemplateExt` contains an entry with `(type, name)` and yields
a warning otherwise. If `template` is provided, it will add such an entry instead of yielding a
warning.

`ref` is the syntax piece. If `name` is not provided, it will use `ident.getId`.
I used this workaround, because I needed a new name (with correct namespace etc)
to be used, and I don't know how to create a new ident with same position but different name.
-/
def checkInventoryDoc (type : InventoryType) (ref : Ident) (name : Name := ref.getId)
    (template : Option String := none) : CommandElabM Unit := do
  -- note: `name` is an `Ident` (instead of `Name`) for the log messages.
  let env ← getEnv
  let n := name
  -- Find a key with matching `(type, name)`.
  match (inventoryTemplateExt.getState env).findIdx?
    (fun x => x.name == n && x.type == type) with
  -- Nothing to do if the entry exists
  | some _ => pure ()
  | none =>
    match template with
    -- Warn about missing documentation
    | none =>
      let docstring ← match (← getDocstring env name type) with
      | some ds =>
        logInfoAt ref (m!"Missing {type} Documentation. Using existing docstring. " ++
        m!"Add {name}\nAdd `{type}Doc {name}` somewhere above this statement.")
        pure s!"*(lean docstring)*\\\n{ds}"
      | none =>
        logWarningAt ref (m!"Missing {type} Documentation: {name}\nAdd `{type}Doc {name}` " ++
        m!"somewhere above this statement.")
        pure "(missing)"

      -- We just add a dummy entry
      modifyEnv (inventoryTemplateExt.addEntry · {
        type := type
        name := name
        category := if type == .Lemma then s!"{n.getPrefix}" else ""
        content := docstring})
    -- Add the default documentation
    | some s =>
      modifyEnv (inventoryTemplateExt.addEntry · {
        type := type
        name := name
        category := if type == .Lemma then s!"{n.getPrefix}" else ""
        content := s })
      logInfoAt ref (m!"Missing {type} Documentation: {name}, used default (e.g. provided " ++
        m!"docstring) instead. If you want to write a different description, add " ++
        m!"`{type}Doc {name}` somewhere above this statement.")

partial def collectUsedInventory (stx : Syntax) (acc : UsedInventory := {}) : CommandElabM UsedInventory := do
  match stx with
  | .missing => return acc
  | .node _info ``GameServer.Tactic.Branch _args => return acc
  | .node _info ``GameServer.Tactic.Hint _args => return acc
  | .node _info _kind args =>
    return ← args.foldlM (fun acc arg => collectUsedInventory arg acc) acc
  | .atom _info val =>
    -- ignore syntax elements that do not start with a letter
    -- and ignore some standard keywords
    let allowed := GameServer.ALLOWED_KEYWORDS
    if 0 < val.length ∧ val.data[0]!.isAlpha ∧ not (allowed.contains val) then
      return {acc with tactics := acc.tactics.insert val}
    else
      return acc
  | .ident _info _rawVal val _preresolved =>
      let ns ←
        try resolveGlobalConst (mkIdent val)
        catch | _ => pure [] -- catch "unknown constant" error
      return ← ns.foldlM (fun acc n => do
        if let some (.thmInfo ..) := (← getEnv).find? n then
          return {acc with lemmas := acc.lemmas.insertMany ns}
        else
          return {acc with definitions := acc.definitions.insertMany ns}
      ) acc

-- #check expandOptDocComment?

def GameLevel.getInventory (level : GameLevel) : InventoryType → InventoryInfo
| .Tactic => level.tactics
| .Definition => level.definitions
| .Lemma => level.lemmas

def GameLevel.setComputedInventory (level : GameLevel) :
    InventoryType → Array InventoryTile → GameLevel
| .Tactic, v =>     {level with tactics     := {level.tactics     with tiles := v}}
| .Definition, v => {level with definitions := {level.definitions with tiles := v}}
| .Lemma, v =>      {level with lemmas      := {level.lemmas      with tiles := v}}
