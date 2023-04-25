import NNG.Levels.AdvMultiplication.Level_1

Game "NNG"
World "AdvMultiplication"
Level 2
Title "eq_zero_or_eq_zero_of_mul_eq_zero"

open MyNat

Introduction
"
A variant on the previous level.
"

Statement MyNat.eq_zero_or_eq_zero_of_mul_eq_zero
"If $ab = 0$, then at least one of $a$ or $b$ is equal to zero."
    (a b : ℕ) (h : a * b = 0) :
  a = 0 ∨ b = 0 := by
  induction a with d
  left
  rfl
  induction b with e
  right
  rfl
  exfalso
  rw [mul_succ] at h
  rw [add_succ] at h
  exact succ_ne_zero _ h

Conclusion
"

"
