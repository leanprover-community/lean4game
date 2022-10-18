import Lean

import GameServer.Utils
import GameServer.EnvExtensions

open Lean Meta

set_option autoImplicit false

/-! ## Easy metadata -/

section metadata

open Lean Meta Elab Command Term

/-- Create a game with the given identifier as name. -/
elab "Game" n:str : command => do
  gameExt.set {name := n.getString}

/-- Define the current level number. -/
elab "Level" n:num : command => do
  let idx := n.getNat
  setCurLevelIdx idx
  levelsExt.insert idx {index := idx}

/-- Define the title of the current game or current level if some
building a level. -/
elab "Title" t:str : command => do
  let lvlIdx ← getCurLevelIdx
  if lvlIdx > 0 then
    let some lvl := (← levelsExt.find? lvlIdx) | throwError "Unable to find level"
    levelsExt.update lvlIdx {lvl with title := t.getString}
  else
    gameExt.set {← gameExt.get with title := t.getString}

/-- Define the introduction of the current game or current level if some
building a level. -/
elab "Introduction" t:str : command => do
  let lvlIdx ← getCurLevelIdx
  if lvlIdx > 0 then
    let some lvl := (← levelsExt.find? lvlIdx) | throwError "Unable to find level"
    levelsExt.update lvlIdx {lvl with introduction := t.getString}
  else
    gameExt.set {← gameExt.get with introduction := t.getString}

/-- Define the statement of the current level. -/
elab "Statement" sig:declSig val:declVal : command => do
  let lvlIdx ← getCurLevelIdx
  let declName : Name := (← gameExt.get).name ++ ("level" ++ toString lvlIdx : String)
  elabCommand (← `(theorem $(mkIdent declName) $sig $val))
  let (binders, _) := expandDeclSig sig
  let mut nb : Nat := 0
  for arg in binders.getArgs do
    nb := nb + arg[1].getArgs.size
  let some cInfo := (← getEnv).find? declName | throwError "Declaration not found"
  levelsExt.update lvlIdx {← getCurLevel with goal := cInfo.type, intro_nb := nb}
  
/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  let lvlIdx ← getCurLevelIdx
  if lvlIdx > 0 then
    let some lvl := (← levelsExt.find? lvlIdx) | throwError "Unable to find level"
    levelsExt.update lvlIdx {lvl with conclusion := t.getString}
  else
    gameExt.set {← gameExt.get with conclusion := t.getString}

/-- Print current game for debugging purposes. -/
elab "PrintCurGame" : command => do
  logInfo (repr (← gameExt.get))

/-- Print current level for debugging purposes. -/
elab "PrintCurLevel" : command => do
  match ← levelsExt.find? (← getCurLevelIdx) with
  | some lvl => logInfo (repr lvl)
  | none => logInfo "Could not find level"

/-- Print levels for debugging purposes. -/
elab "PrintLevels" : command => do
  logInfo $ repr $ (levelsExt.getState (← getEnv)).toList.map (·.fst)

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
  let g ← liftTermElabM do (return ← instantiateMVars (← elabTerm g none))
  let (ctx_size, normalized_goal) ← liftTermElabM do
    let msg_mvar ← mkFreshExprMVar g MetavarKind.syntheticOpaque
    msg_mvar.mvarId!.withContext do 
      let (_, msg_mvar) ← msg_mvar.mvarId!.introNP decls.size
      return ((← msg_mvar.getDecl).lctx.size,  (← normalizedRevertExpr msg_mvar))
  let lvlIdx ← getCurLevelIdx
  let lvl ← getCurLevel
  levelsExt.update lvlIdx {lvl with messages := lvl.messages.push {
    ctx_size := ctx_size,
    normalized_goal := normalized_goal,
    intro_nb := decls.size,
    message := msg.getString }}

/-- Declare a message in reaction to a given tactic state in the current level. -/
macro "Message" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  `(set_option linter.unusedVariables false in Message' $decls* : $goal => $msg)


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
  let lvlIdx ← getCurLevelIdx
  if lvlIdx > 0 then
    let some lvl := (← levelsExt.find? lvlIdx) | throwError "Unable to find level"
    levelsExt.update lvlIdx {lvl with tactics := tactics}
  else
    throwError "This command can be used only while building a level."

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
  let lvlIdx ← getCurLevelIdx
  if lvlIdx > 0 then
    let some lvl := (← levelsExt.find? lvlIdx) | throwError "Unable to find level"
    levelsExt.update lvlIdx {lvl with lemmas := lemmas}
  else
    throwError "This command can be used only while building a level."
