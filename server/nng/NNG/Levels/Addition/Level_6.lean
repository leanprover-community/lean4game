import NNG.Levels.Addition.Level_5

Game "NNG"
World "Addition"
Level 6
Title "add_right_comm"

open MyNat

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


"

Statement MyNat.add_right_comm
"For all natural numbers $a, b$ and $c$, we have
$a + b + c = a + c + b$."
    (a b c : ℕ) : a + b + c = a + c + b := by
  Hint (hidden := true) "You want to change your goal to `a + (b + c) = _`
  so that you can then use commutativity."
  rw [add_assoc]
  Hint "Here you need to be more precise about where to rewrite theorems.
  `rw [add_comm]` will just find the
  first `_ + _` it sees and swap it around. You can target more specific
  additions like this: `rw [add_comm a]` will swap around
  additions of the form `a + _`, and `rw [add_comm a b]` will only
  swap additions of the form `a + b`."
  Branch
    rw [add_comm]
    Hint "`rw [add_comm]` just rewrites to first instance of `_ + _` it finds, which
    is not what you want to do here. Instead you can provide the arguments explicitely:

    * `rw [add_comm b c]`
    * `rw [add_comm b]`
    * `rw [add_comm b _]`
    * `rw [add_comm _ c]`

    would all have worked. You should go back and try again.
    "
  rw [add_comm b c]
  Branch
    rw [add_assoc]
    rfl
  rw [←add_assoc]
  rfl

LemmaTab "Add"

Conclusion
"
If you have got this far, then you have become very good at
manipulating equalities in Lean. You can also now collect
four collectibles (or `instance`s, as Lean calls them)

```
MyNat.addSemigroup     -- (after level 2)
MyNat.addMonoid        -- (after level 2)
MyNat.addCommSemigroup -- (after level 4)
MyNat.addCommMonoid    -- (after level 4)
```

These say that `ℕ` is a commutative semigroup/monoid.

In Multiplication World you will be able to collect such
advanced collectibles as `MyNat.commSemiring` and
`MyNat.distrib`, and then move on to power world and
the famous collectible at the end of it.

One last thing -- didn't you think that solving this level
`add_right_comm` was boring? Check out this AI that can do it for us.

From now on, the `simp` AI becomes accessible (it's just an advanced
tactic really), and can nail some really tedious-for-a-human-to-solve
goals. For example check out this one-line proof:

```
example (a b c d e : ℕ ) :
    (((a + b) + c) + d) + e = (c + ((b + e) + a)) + d := by
  simp
```

Imagine having to do that one by hand! The AI closes the goal
because it knows how to use associativity and commutativity
sensibly in a commutative monoid.

You are now done with addition world. Go back to the main menu (top left)
and decide whether to press on with multiplication world and power world
(which can be solved with `rw`, `refl` and `induction`), or to go on
to Function World where you can learn the tactics needed to prove
goals of the form $P\\implies Q$, thus enabling you to solve more
advanced addition world levels such as $a+t=b+t\\implies a=b$. Note that
Function World is more challenging mathematically; but if you can do Addition
World you can surely do Multiplication World and Power World.
"

-- First we have to get the `AddCommMonoid` collectible,
-- which we do by saying the magic words which make Lean's type class inference
-- system give it to us.
-- -/
-- instance : add_comm_monoid mynat := by structure_helper
