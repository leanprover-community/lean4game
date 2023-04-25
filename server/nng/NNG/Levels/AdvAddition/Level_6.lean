import NNG.Levels.AdvAddition.Level_5

Game "NNG"
World "AdvAddition"
Level 6
Title "add_left_cancel"

open MyNat

Introduction
"
The theorem `add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `t + a = t + b` then `a = b`.
"

Statement MyNat.add_left_cancel
"On the set of natural numbers, addition has the left cancellation property.
In other words, if there are natural numbers $a, b$ and $t$ such that
$$ t + a = t + b, $$
then we have $a = b$."
    (t a b : ℕ) : t + a = t + b → a = b := by
  Hint "There is a three-line proof which ends in `exact add_right_cancel a t b` (or even
  `exact add_right_cancel _ _ _`); this
  strategy involves changing the goal to the statement of `add_right_cancel` somehow."
  rw [add_comm]
  rw [add_comm t]
  Hint "Now that looks like `add_right_cancel`!"
  Hint (hidden := true) "`exact add_right_cancel` does not work. You need
  `exact add_right_cancel a t b` or `exact add_right_cancel _ _ _`."
  exact add_right_cancel a t b

LemmaTab "Add"

Conclusion
"

"
