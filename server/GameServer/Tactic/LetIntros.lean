import Lean.Elab.Binders
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Intro

/-!
# `let_intros` Tactic

`let_intros` is a weaker form of `intros` aimed to only introduce `let` statements,
but not for example `∀`-binders.

Note: Mathlib has a tactic `extract_lets` which does essentially exactly this.
  The only difference is that `let_intros` is unhygenic, in the sense that it will name
  the introduced variables `f` instead of leaving them inaccessible `f✝`.
-/

namespace GameServer

open Lean Meta Elab Parser Tactic

/--
Copied from `Lean.Meta.getIntrosSize`.
-/
private partial def getLetIntrosSize : Expr → Nat
  -- | .forallE _ _ b _ => getLetIntrosSize b + 1
  | .letE _ _ _ b _  => getLetIntrosSize b + 1
  | .mdata _ b       => getLetIntrosSize b
  | e                =>
    if let some (_, _, _, b) := e.letFun? then
      getLetIntrosSize b + 1
    else
      0

/--
Copied and from `Lean.MVarId.intros`.
-/
def _root_.Lean.MVarId.letIntros (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let n := getLetIntrosSize type
  if n == 0 then
    return (#[], mvarId)
  else
    -- `introNP` preserves the binder names
    mvarId.introNP n

/--
`let_intros` introduces all `let` statements that are preceding the proof. Concretely
it does a subset of what `intros` does.

If names are provided, it will introduce as many `let` statements as there are names.
-/
syntax (name := letIntros) "let_intros" : tactic
-- (ppSpace colGt (ident <|> hole))*

@[tactic letIntros] def evalLetIntros : Tactic := fun stx => do
  match stx with
  | `(tactic| let_intros) => liftMetaTactic fun mvarId => do
    let (_, mvarId) ← mvarId.letIntros
    return [mvarId]
  -- | `(tactic| let_intros $ids*) => do
  --   let fvars ← liftMetaTacticAux fun mvarId => do
  --     let (fvars, mvarId) ← mvarId.introN ids.size (ids.map getNameOfIdent').toList
  --     return (fvars, [mvarId])
  --   withMainContext do
  --     for stx in ids, fvar in fvars do
  --       Term.addLocalVarInfo stx (mkFVar fvar)
  | _ => throwUnsupportedSyntax
