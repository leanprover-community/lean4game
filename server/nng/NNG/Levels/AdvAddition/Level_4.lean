import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 4
Title "eq_iff_succ_eq_succ"

open MyNat

Introduction
"
Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `split` tactic, which is how you're going to have to start.

`split,`

Now you have two goals. The first is exactly `succ_inj` so you can close
it with

`exact succ_inj,`

and the second one you could solve by looking up the name of the theorem
you proved in the last level and doing `exact <that name>`, or alternatively
you could get some more `intro` practice and seeing if you can prove it
using `intro`, `rw` and `refl`.
"

Statement
"Two natural numbers are equal if and only if their successors are equal.
"
    (a b : ℕ) : succ a = succ b ↔ a = b := by
  constructor
  exact succ_inj
  intro H
  rw [H]
  rfl

Conclusion
"

"
