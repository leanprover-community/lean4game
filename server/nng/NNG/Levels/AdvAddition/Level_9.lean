import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 9
Title "succ_ne_zero"

open MyNat

Introduction
"
Levels 9 to 13 introduce the last axiom of Peano, namely
that $0\\not=\\operatorname{succ}(a)$. The proof of this is called `zero_ne_succ a`. 

`zero_ne_succ (a : mynat) : 0 ≠ succ(a)`

The `symmetry` tactic will turn any goal of the form `R x y` into `R y x`,
if `R` is a symmetric binary relation (for example `=` or `≠`).
In particular, you can prove `succ_ne_zero` below by first using
`symmetry` and then `exact zero_ne_succ a`. 
"

Statement -- succ_ne_zero
"Zero is not the successor of any natural number."
    (a : ℕ) : succ a ≠ 0 := by
  apply Ne.symm
  exact zero_ne_succ a


Conclusion
"

"
