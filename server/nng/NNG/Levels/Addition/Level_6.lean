import NNG.Metadata
import NNG.MyNat.Addition
import NNG.Levels.Addition.Level_5

Game "NNG"
World "Addition"
Level 6
Title "add_right_comm"

open MyNat

namespace AdditionWorld

Introduction
"
Lean sometimes writes `a + b + c`. What does it mean? The convention is
that if there are no brackets displayed in an addition formula, the brackets
are around the left most `+` (Lean's addition is \"left associative\").
So the goal in this level is `(a + b) + c = (a + c) + b`. This isn't
quite `add_assoc` or `add_comm`, it's something you'll have to prove
by putting these two theorems together.

If you hadn't picked up on this already, `rw [add_assoc]` will
change `(x + y) + z` to `x + (y + z)`, but to change it back
you will need `rw [← add_assoc]`. Get the left arrow by typing `\\l`
then the space bar (note that this is L for left, not a number 1).
Similarly, if `h : a = b` then `rw [h]` will change `a`'s to `b`'s
and `rw [← h]` will change `b`'s to `a`'s.

Also, you can be (and will need to be, in this level) more precise
about where to rewrite theorems. `rw add_comm,` will just find the
first `? + ?` it sees and swap it around. You can target more specific
additions like this: `rw add_comm a` will swap around
additions of the form `a + ?`, and `rw add_comm a b,` will only
swap additions of the form `a + b`.
"

Statement --add_right_comm
"For all natural numbers $a, b$ and $c$, we have
$a + b + c = a + c + b$."
    (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [←add_assoc]
  rfl

Conclusion
"
"
