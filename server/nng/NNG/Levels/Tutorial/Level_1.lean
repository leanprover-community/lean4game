import NNG.Metadata
import NNG.MyNat.Multiplication

Game "NNG"
World "Tutorial"
Level 1
Title "The rfl tactic"

Introduction
"
Each level in this game involves proving a mathematical statement. In this first level
you have three natural numbers $x, y, z$ (listed under \"Objects\") and you want to prove
$xy + z = xy + z$ (displayed under \"Goal\").

You can modify the Goal using *Tactics* until you can close it (i.e. prove it).

The first tactic is called `rfl`, which stands for \"reflexivity\",
a fancy way of saying that it will prove any goal of the form `A = A`. It doesn't matter how
complicated `A` is, all that matters is that the left hand side is exactly equal to the right hand
side. I really mean \"press the same buttons
on your computer in the same order\" equal. For example, `x * y + z = x * y + z` can be proved by `rfl`,
but `x + y = y + x` cannot.
"

Statement
"For all natural numbers $x, y$ and $z$, we have $xy + z = xy + z$."
    (x y z : ℕ) : x * y + z = x * y + z := by
  Hint "In order to use the tactic `rfl` you can enter it above and hit \"Execute\"."
  rfl

NewTactic rfl
NewDefinition MyNat

Conclusion
"
Congratulations! You completed your first verified proof!

If you want to be reminded about the `rfl` tactic, your inventory on the right contains useful
information about things you've learned.

Now click on \"Next\" to continue the journey.
"
