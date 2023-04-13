import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 6
Title "add_left_cancel"

open MyNat

Introduction
"
The theorem `add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `t + a = t + b` then `a = b`. 
There is a three-line proof which ends in `exact add_right_cancel a t b` (or even
`exact add_right_cancel _ _ _`); this
strategy involves changing the goal to the statement of `add_right_cancel` somehow.

"

Statement
"On the set of natural numbers, addition has the left cancellation property.
In other words, if there are natural numbers $a, b$ and $t$ such that
$$ t + a = t + b, $$
then we have $a = b$."
    (t a b : ℕ) : t + a = t + b → a = b := by
  rw [add_comm]
  rw [add_comm t]
  exact add_right_cancel a t b

Conclusion
"

"
