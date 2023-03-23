import Lean
-- import TestGame.MyNat

open Lean Elab Tactic

elab "swap" : tactic => do
  match ← getGoals with
  | g₁::g₂::t => setGoals (g₂::g₁::t)
  | _ => pure ()

-- macro "induction_on" n:ident : tactic =>
-- `(tactic| refine myInduction $n ?base ?inductive_step; swap; clear $n; intro $n $(mkIdent `ind_hyp); swap)
