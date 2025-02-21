/- Modified from Mathlib.Tactic.HelpCmd -/
import Lean

open Lean Meta Elab Tactic Command Expr

/-- Gets the initial string token in a parser description. For example, for a declaration like
`syntax "bla" "baz" term : tactic`, it returns `some "bla"`. Returns `none` for syntax declarations
that don't start with a string constant. -/
partial def getHeadTk (e : Expr) : Option String :=
  match (withApp e λ e a => (e.constName?.getD Name.anonymous, a)) with
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

def getTacticDocstring (name: Name) : CommandElabM String := do
  let name := name.toString (escape := false)
  let mut decls : Lean.RBMap String (Array SyntaxNodeKind) compare := {}

  let env ← getEnv

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
  return ""

/-- info: "The `simp` tactic" -/
#guard_msgs in
#eval do
  let doc ← (getTacticDocstring `simp)
  return doc.take 17

    -- TODO: Things we want:
    -- 1) Getting docstring this way is a problem if we want to "reprove" a mathlib theorem because
    -- either it would not be imported from mathlib or have a different name in `Statement`
    -- 3) is the theorem a simp theorem? (are there other attributes on it? --> hard/impossible)
    -- 4) which mathlib file is it imported from?
    -- 5) namespace
    -- 6) tactics: are there alternative variations like `ext`, `ext?`, `ext1?`, …
    -- 7) definition: is it reducible?
    -- .) …
