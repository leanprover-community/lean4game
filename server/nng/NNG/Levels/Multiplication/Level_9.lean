import NNG.Levels.Multiplication.Level_8

Game "NNG"
World "Multiplication"
Level 9
Title "mul_left_comm"

open MyNat

Introduction
"
You are equipped with

* `mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c)`
* `mul_comm (a b : ℕ) : a * b = b * a`

Re-read the docs for `rw` so you know all the tricks.
You can see them in your inventory on the right.

"

Statement MyNat.mul_left_comm
"For all natural numbers $a$ $b$ and $c$, we have $a(bc)=b(ac)$."
    (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]
  rfl

LemmaTab "Mul"

-- TODO: make simp work:
-- attribute [simp] mul_assoc mul_comm mul_left_comm

Conclusion
"
And now I whisper a magic incantation

```
attribute [simp] mul_assoc mul_comm mul_left_comm
```

and all of a sudden Lean can automatically do levels which are
very boring for a human, for example

```
example (a b c d e : ℕ) :
    (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d := by
  simp
```

If you feel like attempting Advanced Multiplication world
you'll have to do Function World and the Proposition Worlds first.
These worlds assume a certain amount of mathematical maturity
(perhaps 1st year undergraduate level).
Your other possibility is Power World, with the \"final boss\".
"
