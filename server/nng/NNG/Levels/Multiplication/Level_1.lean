import NNG.MyNat.Multiplication
import NNG.Levels.Addition

Game "NNG"
World "Multiplication"
Level 1
Title "zero_mul"

open MyNat

Introduction
"
As a side note, the lemmas about addition are still available in your inventory
in the lemma tab \"Add\" while the new lemmas about multiplication appear in the
tab \"Mul\".

We are given `mul_zero`, and the first thing to prove is `zero_mul`.
Like `zero_add`, we of course prove it by induction.
"

Statement MyNat.zero_mul
"For all natural numbers $m$, we have $ 0 \\cdot m = 0$."
    (m : ℕ) : 0 * m = 0 := by
  induction m
  rw [mul_zero]
  rfl
  rw [mul_succ]
  rw [n_ih]
  rw [add_zero]
  rfl

NewTactic simp
NewLemma MyNat.mul_zero MyNat.mul_succ
NewDefinition Mul
LemmaTab "Mul"
