import NNG.Levels.AdvAddition.Level_3

Game "NNG"
World "AdvAddition"
Level 4
Title "eq_iff_succ_eq_succ"

open MyNat

Introduction
"
Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `constructor` tactic, which is how you're going to have to start.
"

Statement
"Two natural numbers are equal if and only if their successors are equal.
"
    (a b : ℕ) : succ a = succ b ↔ a = b := by
  constructor
  Hint "Now you have two goals. The first is exactly `succ_inj` so you can close
  it with

  ```
  exact succ_inj
  ```
  "
  · exact succ_inj
  · Hint "The second one you could solve by looking up the name of the theorem
    you proved in the last level and doing `exact <that name>`, or alternatively
    you could get some more `intro` practice and seeing if you can prove it
    using `intro`, `rw` and `rfl`."
    Branch
      exact succ_eq_succ_of_eq
    intro h
    rw [h]
    rfl

LemmaTab "Nat"

Conclusion
"

"
