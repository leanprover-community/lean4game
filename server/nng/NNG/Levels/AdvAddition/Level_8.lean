import NNG.Levels.AdvAddition.Level_7


Game "NNG"
World "AdvAddition"
Level 8
Title "eq_zero_of_add_right_eq_self"

open MyNat

Introduction
"
The lemma you're about to prove will be useful when we want to prove that $\\leq$ is antisymmetric.
There are some wrong paths that you can take with this one.
"

Statement MyNat.eq_zero_of_add_right_eq_self
"If $a$ and $b$ are natural numbers such that
$$ a + b = a, $$
then $b = 0$."
    {a b : ℕ} : a + b = a → b = 0 := by
  intro h
  Hint (hidden := true) "Look at `add_left_cancel`."
  apply add_left_cancel a
  rw [h]
  rw [add_zero]
  rfl

LemmaTab "Add"

Conclusion
"

"
