import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 5
Title "add_right_cancel"

open MyNat

Introduction
"
The theorem `add_right_cancel` is the theorem that you can cancel on the right
when you're doing addition -- if `a + t = b + t` then `a = b`. After `intro h`
I'd recommend induction on `t`. Don't forget that `rw add_zero at h` can be used
to do rewriting of hypotheses rather than the goal.
"

Statement
"On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + t = b + t, $$
then we have $a = b$."
    (a t b : ℕ) : a + t = b + t → a = b := by
  intro h
  induction t with d hd
  rw [add_zero] at h
  rw [add_zero] at h
  exact h
  apply hd
  rw [add_succ] at h
  rw [add_succ] at h
  exact succ_inj h

Conclusion
"

"
