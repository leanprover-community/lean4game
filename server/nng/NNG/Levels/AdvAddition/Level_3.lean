import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 3
Title "succ_eq_succ_of_eq"

open MyNat

Introduction
"
We are going to prove something completely obvious: if $a=b$ then
$succ(a)=succ(b)$. This is *not* `succ_inj`!
This is trivial -- we can just rewrite our proof of `a=b`.
But how do we get to that proof? Use the `intro` tactic.
"

Statement
"For all naturals $a$ and $b$, $a=b\\implies succ(a)=succ(b)$. 
"
    {a b : ℕ} : a = b → succ a = succ b := by
  intro h
  rw [h]
  rfl

Conclusion
"

"
