import NNG.Levels.AdvAddition.Level_10

Game "NNG"
World "AdvAddition"
Level 11
Title "add_right_eq_zero"

open MyNat

Introduction
"
We just proved `add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0`.
Hopefully `add_right_eq_zero` shouldn't be too hard now.
"

Statement MyNat.add_right_eq_zero
"If $a$ and $b$ are natural numbers such that
$$ a + b = 0, $$
then $a = 0$."
    {a b : ℕ} : a + b = 0 → a = 0 := by
  intro h
  rw [add_comm] at h
  exact add_left_eq_zero h

LemmaTab "Add"

Conclusion
"

"
