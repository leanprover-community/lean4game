import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 7
Title "add_right_cancel_iff"

open MyNat

Introduction
"
It's sometimes convenient to have the \"if and only if\" version
of theorems like `add_right_cancel`. Remember that you can use `split`
to split an `↔` goal into the `→` goal and the `←` goal.

## Pro tip:

`exact add_right_cancel _ _ _` means \"let Lean figure out the missing inputs\"
"

Statement --add_right_cancel_iff 
"For all naturals $a$, $b$ and $t$, 
$$ a + t = b + t\\iff a=b. $$
"
    (t a b : ℕ) :  a + t = b + t ↔ a = b := by
  constructor
  exact add_right_cancel _ _ _ -- done that way already,
  intro H -- H : a = b,
  rw [H]
  rfl
Conclusion
"

"
