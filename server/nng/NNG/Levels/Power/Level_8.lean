import NNG.Levels.Power.Level_7
-- import Mathlib.Tactic.Ring

Game "NNG"
World "Power"
Level 8
Title "add_squared"

open MyNat

Introduction
"
[final boss music] 

You see something written on the stone dungeon wall:
```
by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  repeat rw [pow_succ]
  …
```

and you can't make out the last two lines because there's a kind
of thing in the way that will magically disappear
but only when you've beaten the boss.
"

Statement MyNat.add_squared
"For all naturals $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2ab.$$"
  (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  repeat rw [pow_succ]
  repeat rw [pow_zero]
  --ring
  repeat rw [one_mul]
  rw [add_mul, mul_add, mul_add, mul_comm b a]
  rw [succ_mul, succ_mul, zero_mul, zero_add, add_mul]
  repeat rw [add_assoc]
  rw [add_comm _ (b * b), ← add_assoc _ (b*b), add_comm _ (b*b), add_assoc]
  rfl

NewLemma MyNat.two_eq_succ_one
LemmaTab "Pow"

Conclusion
"

"
