import Mathlib.Lean.Expr.Basic
import NNG.MyNat.Addition
import Lean.Elab.Tactic.Basic

/-!
# Modified `rw`

Modify `rw` to work like `rewrite`.

This is mainly a copy of the implementation of `rewrite` in Lean core.
-/

namespace MyNat

open Lean.Meta Lean.Elab.Tactic Lean.Parser.Tactic

/--
Modified `rw` tactic. For this game, `rw` works exactly like `rewrite`.
-/
syntax (name := rewriteSeq) "rw" (config)? rwRuleSeq (location)? : tactic

@[tactic MyNat.rewriteSeq] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

/-!
# Modified `induction` tactic

Modify `induction` tactic to always show `(0 : MyNat)` instead of `MyNat.zero` and
to support the lean3-style `with` keyword.

This is mainly copied and modified from the mathlib-tactic `induction'`.
-/

def rec' {P : ℕ → Prop} (zero : P 0)
    (succ : (n : ℕ) → (n_ih : P n) → P (succ n)) (t : ℕ) : P t := by
  induction t with
  | zero => assumption
  | succ n =>
    apply succ
    assumption

end MyNat

namespace Lean.Parser.Tactic
open Meta Elab Elab.Tactic

open private getAltNumFields in evalCases ElimApp.evalAlts.go in
def ElimApp.evalNames (elimInfo : ElimInfo) (alts : Array ElimApp.Alt) (withArg : Syntax)
    (numEqs := 0) (numGeneralized := 0) (toClear : Array FVarId := #[]) :
    TermElabM (Array MVarId) := do
  let mut names : List Syntax := withArg[1].getArgs |>.toList
  let mut subgoals := #[]
  for { name := altName, mvarId := g, .. } in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields (Unhygienic.run `(_))
    names := names'
    let (fvars, g) ← g.introN numFields <| altVarNames.map (getNameOfIdent' ·[0])
    let some (g, subst) ← Cases.unifyEqs? numEqs g {} | pure ()
    let (_, g) ← g.introNP numGeneralized
    let g ← liftM $ toClear.foldlM (·.tryClear) g
    for fvar in fvars, stx in altVarNames do
      g.withContext <| (subst.apply <| .fvar fvar).addLocalVarInfoForBinderIdent ⟨stx⟩
    subgoals := subgoals.push g
  pure subgoals

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in

/--
Modified `induction` tactic for this game.

Usage: `induction n with d hd`.

*(The actual `induction` tactic has a more complex `with`-argument that works differently)*
-/
elab (name := _root_.MyNat.induction) "induction " tgts:(casesTarget,+)
    withArg:((" with " (colGt binderIdent)+)?)
    : tactic => do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimInfo `MyNat.rec'
    let targets ← addImplicitTargets elimInfo targets
    evalInduction.checkTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    g.withContext do
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      let (fvarIds, g) ← g.revert (← sortFVarIds s.toArray)
      let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
      let elimArgs := result.elimApp.getAppArgs
      ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
        (numGeneralized := fvarIds.size) (toClear := targetFVarIds)
      setGoals <| (subgoals ++ result.others).toList ++ gs

end Lean.Parser.Tactic


/-! # `rfl` tactic

Added `withReducible` to prevent `rfl` proving stuff like `n + 0 = n`.
-/

namespace MyNat

open Lean Meta Elab Tactic

-- @[match_pattern] def MyNat.rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-- Modified `rfl` tactic.

`rfl` closes goals of the form `A = A`.

Note that teh version for this game is somewhat weaker than the real one. -/
syntax (name := rfl) "rfl" : tactic

@[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do withReducible <| mvarId.refl; pure []

-- @[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
--   liftMetaTactic fun mvarId => do mvarId.refl; pure []
-- (with_reducible rfl)

end MyNat
