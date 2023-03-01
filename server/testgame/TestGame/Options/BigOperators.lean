import Mathlib.Algebra.BigOperators.Fin

open BigOperators

open Lean PrettyPrinter Delaborator SubExpr

@[ delab app.Finset.sum]
def delabFinsetSum : Delab := do
  guard $ (← getExpr).getAppNumArgs == 5
  guard $ ((← getExpr).getArg! 3).isAppOf' ``Finset.univ
  guard $ ((← getExpr).getArg! 4).isLambda
  withNaryArg 4 do
    let α ← withBindingDomain delab
    withBindingBodyUnusedName fun n => do
      let n : TSyntax `ident := ⟨n⟩
      let b ← delab
      `(∑ $n:ident : $α, $b)
