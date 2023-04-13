import NNG.Metadata
import NNG.MyNat.LE
import Mathlib.Tactic.Use

Game "NNG"
World "Inequality"
Level 2
Title "le_rfl"

open MyNat

Introduction
"
Here's a nice easy one.
"

Statement
"The $\\le$ relation is reflexive. In other words, if $x$ is a natural number,
then $x\\le x$."
    (x : ℕ) : x ≤ x := by
  use 0
  rw [add_zero]
  rfl

Conclusion
"

"
