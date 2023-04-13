import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 11
Title "add_right_eq_zero"

open MyNat

theorem MyNat.add_left_eq_zero {{a b : ℕ}} (H : a + b = 0) : b = 0 := by sorry

Introduction
"
We just proved `add_left_eq_zero (a b : mynat) : a + b = 0 → b = 0`.
Hopefully `add_right_eq_zero` shouldn't be too hard now.
"

Statement
"If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $a = 0$."
    {a b : ℕ} : a + b = 0 → a = 0 := by
  intro H
  rw [add_comm] at H
  exact add_left_eq_zero H

Conclusion
"

"
