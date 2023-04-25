import NNG.Levels.AdvMultiplication.Level_2


Game "NNG"
World "AdvMultiplication"
Level 3
Title "mul_eq_zero_iff"

open MyNat

Introduction
"
Now you have `eq_zero_or_eq_zero_of_mul_eq_zero` this is pretty straightforward.
"

Statement
"$ab = 0$, if and only if at least one of $a$ or $b$ is equal to zero.
"
    {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  intro h
  exact eq_zero_or_eq_zero_of_mul_eq_zero a b h
  intro hab
  rcases hab with hab | hab
  rw [hab]
  rw [zero_mul]
  rfl
  rw [hab]
  rw [mul_zero]
  rfl


Conclusion
"

"
