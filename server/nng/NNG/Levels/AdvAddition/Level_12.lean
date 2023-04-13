import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 12
Title "add_one_eq_succ"

open MyNat

Introduction
"
We have

  * `succ_eq_add_one (n : mynat) : succ n = n + 1`

but sometimes the other way is also convenient.
"

theorem succ_eq_add_one (d : ℕ) : succ d = d + 1 := by sorry

Statement
"For any natural number $d$, we have
$$ d+1 = \\operatorname{succ}(d). $$"
    (d : ℕ) : d + 1 = succ d := by
  rw [succ_eq_add_one]
  rfl

Conclusion
"

"
