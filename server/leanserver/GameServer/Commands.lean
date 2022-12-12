import Lean

import GameServer.EnvExtensions

open Lean Meta

set_option autoImplicit false

/-! ## Easy metadata -/

section metadata

open Lean Meta Elab Command Term

/-- Create a game with the given identifier as name. -/
elab "Game" n:str : command => do
  let name := n.getString
  setCurGameId name
  if (← getGame? name).isNone then
    insertGame name {name}

/-- Create a World -/
elab "World" n:str : command => do
  let name := n.getString
  setCurWorldId name
  if ¬ (← getCurGame).worlds.nodes.contains name then
    addWorld {name}

/-- Define the current level number. -/
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

-- TODO: Instead of this, it would be nice to have a proper syntax parser that enables
-- us highlighting on the client side.
partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ kind args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.joinSep args " "

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

-- macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

/-- Define the statement of the current level.

Arguments:
- ident: (Optional) The name of the statemtent.
- descr: The human-readable version of the lemma as string. Accepts Markdown and Mathjax.
-/
elab "Statement" statementName:ident ? descr:str sig:declSig val:declVal : command => do

  let lvlIdx ← getCurLevelIdx
  let defaultDeclName : Name := (← getCurGame).name ++ (← getCurWorld).name ++
    ("level" ++ toString lvlIdx : String)
  let thmStatement ← `(theorem $(mkIdent defaultDeclName) $sig $val)
  -- let thmStatement' ← match statementName with
  -- | none => `(lemma $(mkIdent "XX") $sig $val) -- TODO: Make it into an `example`
  -- | some name => `(lemma $name $sig $val)

  elabCommand thmStatement
  modifyCurLevel fun level => pure {level with
    goal := sig,
    description := descr.getString,
    ppStatement := match statementName with
    | none => "example " ++ (toString <| reprint sig.raw) ++ " := by"
    | some name => (Format.join ["lemma ", reprint name.raw, " ", reprint sig.raw, " := by"]).pretty 10  -- "lemma "  ++ (toString <| reprint name.raw) ++ " " ++ (Format.pretty (reprint sig.raw) 40) ++ " := by"
  } -- Format.pretty <| format thmStatement.raw }

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := t.getString}

-- /-- Print current game for debugging purposes. -/
-- elab "PrintCurGame" : command => do
--   logInfo (toJson (← getCurGame))

/-- Print current level for debugging purposes. -/
elab "PrintCurLevel" : command => do
  logInfo (repr (← getCurLevel))

-- /-- Print levels for debugging purposes. -/
elab "PrintLevels" : command => do
  logInfo $ repr $ (← getCurWorld).levels.toArray

def Parser.path := Parser.sepBy1Indent Parser.ident "→"

elab "Path" s:Parser.path : command => do
  let mut last : Option Name := none
  for stx in s.raw.getArgs.getEvenElems do
    let some l := last
      | do
          last := some stx.getId
          continue
    modifyCurGame fun game =>
      pure {game with worlds := {game.worlds with edges := game.worlds.edges.push (l, stx.getId)}}
    last := some stx.getId

end metadata

/-! ## Messages -/

open Lean Meta Elab Command Term

declare_syntax_cat mydecl
syntax "(" ident ":" term ")" : mydecl

def getIdent : TSyntax `mydecl → Ident
| `(mydecl| ($n:ident : $_t:term)) => n
| _ => default

def getType : TSyntax `mydecl → Term
| `(mydecl| ($_n:ident : $t:term)) => t
| _ => default

/-- From a term `s` and a list of pairs `(i, t) ; Ident × Term`, create the syntax
where `s` is preceded with universal quantifiers `∀ i : t`. -/
def mkGoalSyntax (s : Term) : List (Ident × Term) → MacroM Term
| (n, t)::tail => do return (← `(∀ $n : $t, $(← mkGoalSyntax s tail)))
| [] => return s

/-- Declare a message. This version doesn't prevent the unused linter variable from running. -/
local elab "Message'" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  let g ← liftMacroM $ mkGoalSyntax goal (decls.map (λ decl => (getIdent decl, getType decl))).toList
  let g ← liftTermElabM do (return ← elabTermAndSynthesize g none)
  modifyCurLevel fun level => pure {level with messages := level.messages.push {
    goal := g,
    intros := decls.size,
    message := msg.getString }}

/--
Declare a hint. This version doesn't prevent the unused linter variable from running.
The difference between hints/messages is that hints should be hidden by default, while
messages are visible.
-/
local elab "Hint'" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  let g ← liftMacroM $ mkGoalSyntax goal (decls.map (λ decl => (getIdent decl, getType decl))).toList
  let g ← liftTermElabM do (return ← elabTermAndSynthesize g none)
  modifyCurLevel fun level => pure {level with messages := level.messages.push {
    goal := g,
    intros := decls.size,
    spoiler := true,
    message := msg.getString }}


/-- Declare a message in reaction to a given tactic state in the current level. -/
macro "Message" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  `(set_option linter.unusedVariables false in Message' $decls* : $goal => $msg)

/-- Declare a hint in reaction to a given tactic state in the current level. -/
macro "Hint" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  `(set_option linter.unusedVariables false in Hint' $decls* : $goal => $msg)

/-! ## Tactics -/

/-- Declare a documentation entry for some tactic.
Expect an identifier and then a string literal. -/
elab "TacticDoc" name:ident content:str : command =>
  modifyEnv (tacticDocExt.addEntry · {
    name := name.getId,
    content := content.getString })

/-- Declare a set of tactic documentation entries.
Expect an identifier used as the set name then `:=` and a
space separated list of identifiers.
-/
elab "TacticSet" name:ident ":=" args:ident* : command => do
  let docs := tacticDocExt.getState (← getEnv)
  let mut entries : Array TacticDocEntry := #[]
  for arg in args do
    let name := arg.getId
    match docs.find? (·.name = name) with
    | some doc => entries := entries.push doc
    | none => throwError "Documentation for tactic {name} wasn't found."
  modifyEnv (tacticSetExt.addEntry · {
    name := name.getId,
    tactics := entries })

instance : Quote TacticDocEntry `term :=
⟨λ entry => Syntax.mkCApp ``TacticDocEntry.mk #[quote entry.name, quote entry.content]⟩

/-- Declare the list of tactics that will be displayed in the current level.
Expects a space separated list of identifiers that refer to either a tactic doc
entry or a tactic doc set. -/
elab "Tactics" args:ident* : command => do
  let env ← getEnv
  let docs := tacticDocExt.getState env
  let sets := tacticSetExt.getState env
  let mut tactics : Array TacticDocEntry := #[]
  for arg in args do
    let name := arg.getId
    match docs.find? (·.name = name) with
    | some entry => tactics := tactics.push entry
    | none => match sets.find? (·.name = name) with
              | some entry => tactics := tactics ++ entry.tactics
              | none => throwError "Tactic doc or tactic set {name} wasn't found."
  modifyCurLevel fun level => pure {level with tactics := tactics}

/-! ## Lemmas -/

/-- Declare a documentation entry for some lemma.
Expect two identifiers and then a string literal. The first identifier is meant
as the real name of the lemma while the second is the displayed name. Currently
the real name isn't used. -/
elab "LemmaDoc" name:ident "as" userName:ident "in" category:str content:str : command =>
  modifyEnv (lemmaDocExt.addEntry · {
    name := name.getId,
    userName := userName.getId,
    category := category.getString,
    content := content.getString })

/-- Declare a set of lemma documentation entries.
Expect an identifier used as the set name then `:=` and a
space separated list of identifiers. -/
elab "LemmaSet" name:ident ":" title:str ":=" args:ident* : command => do
  let docs := lemmaDocExt.getState (← getEnv)
  let mut entries : Array LemmaDocEntry := #[]
  for arg in args do
    let name := arg.getId
    match docs.find? (·.userName = name) with
    | some doc => entries := entries.push doc
    | none => throwError "Lemma doc {name} wasn't found."
  modifyEnv (lemmaSetExt.addEntry · {
    name := name.getId,
    title := title.getString,
    lemmas := entries })

instance : Quote LemmaDocEntry `term :=
⟨λ entry => Syntax.mkCApp ``LemmaDocEntry.mk #[quote entry.name, quote entry.userName, quote entry.category, quote entry.content]⟩

/-- Declare the list of lemmas that will be displayed in the current level.
Expects a space separated list of identifiers that refer to either a lemma doc
entry or a lemma doc set. -/
elab "Lemmas" args:ident* : command => do
  let env ← getEnv
  let docs := lemmaDocExt.getState env
  let sets := lemmaSetExt.getState env
  let mut lemmas : Array LemmaDocEntry := #[]
  for arg in args do
    let name := arg.getId
    match docs.find? (·.userName = name) with
    | some entry => lemmas := lemmas.push entry
    | none => match sets.find? (·.name = name) with
              | some entry => lemmas := lemmas ++ entry.lemmas
              | none => throwError "Lemma doc or lemma set {name} wasn't found."
  modifyCurLevel fun level => pure {level with lemmas := lemmas}
