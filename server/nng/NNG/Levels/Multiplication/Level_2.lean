import NNG.Levels.Multiplication.Level_1

Game "NNG"
World "Multiplication"
Level 2
Title "mul_one"

open MyNat

Introduction
"
In this level we'll need to use

* `one_eq_succ_zero : 1 = succ 0 `

which was mentioned back in Addition World  (see \"Add\" tab in your inventory) and
which will be a useful thing to rewrite right now, as we
begin to prove a couple of lemmas about how `1` behaves
with respect to multiplication.
"

Statement MyNat.mul_one
"For any natural number $m$, we have $ m \\cdot 1 = m$."
    (m : ℕ) : m * 1 = m := by
rw [one_eq_succ_zero]
rw [mul_succ]
rw [mul_zero]
rw [zero_add]
rfl

LemmaTab "Mul"
