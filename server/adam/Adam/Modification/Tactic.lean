import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Basic
import Mathlib.Init.Data.Nat.Notation

open Lean.Meta Lean.Elab.Tactic Lean.Parser.Tactic

/-!
# Modified `induction` tactic

Modify `induction` tactic to use the cases `0` and `n + 1` (isnstead of `zero` and `succ n`)
and support the lean3-style `with` keyword.

This is mainly copied and modified from the mathlib-tactic `induction'`.
-/

/-- Custom induction principle that uses `0` and `n + 1` instead
of `Nat.zero` and `Nat.succ n`. -/
def CustomTactic.rec' {P : ℕ → Prop} (zero : P 0)
    (succ : (n : ℕ) → (n_ih : P n) → P (n + 1)) (t : ℕ) : P t := by
  induction t with
  | zero => assumption
  | succ n =>
    apply succ
    assumption

namespace Lean.Parser.Tactic
open Meta Elab Elab.Tactic

open private getAltNumFields in evalCases ElimApp.evalAlts.go in
def _root_.CustomTactic.ElimApp.evalNames (elimInfo : ElimInfo) (alts : Array ElimApp.Alt) (withArg : Syntax)
    (numEqs := 0) (numGeneralized := 0) (toClear : Array FVarId := #[]) :
    Lean.Elab.Term.TermElabM (Array MVarId) := do
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

For this game, `induction n` uses the cases `0` and `n + 1` instead of `Nat.zero` and
`Nat.succ n`. These are defEq, but it's currently annoying that `ring` does not like the
latter forms.

*(The actual `induction` tactic has a more complex `with`-argument that works differently)*
-/
elab (name := _root_.MyNat.induction) "induction " tgts:(casesTarget,+)
    withArg:((" with " (colGt binderIdent)+)?)
    : tactic => do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimInfo `CustomTactic.rec'
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
      let subgoals ← CustomTactic.ElimApp.evalNames elimInfo result.alts withArg
        (numGeneralized := fvarIds.size) (toClear := targetFVarIds)
      setGoals <| (subgoals ++ result.others).toList ++ gs

end Lean.Parser.Tactic
