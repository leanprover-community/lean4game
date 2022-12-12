import TestGame.Metadata

Game "TestGame"
World "Old"
Level 1

Title "The reflexivity spell"

Introduction
"
Let's learn a first spell: the `rfl` spell. `rfl` stands for \"reflexivity\", which is a fancy
way of saying that it will prove any goal of the form `A = A`. It doesn't matter how
complicated `A` is, all that matters is that the left hand side is *exactly equal* to the
right hand side (a computer scientist would say \"definitionally equal\"). I really mean
\"press the same buttons on your computer in the same order\" equal.
For example, `x * y + z = x * y + z` can be proved by `rfl`, but `x + y = y + x` cannot.
This is a very low level spell, but you need to start somewhere.

After closing this message, type rfl in the invocation zone and hit Enter or click
the \"Cast spell\" button.
"

Statement "" (x y z : ℕ) :  x * y + z = x * y + z := by
rfl

Conclusion "Congratulations for completing your first level! You can now click on the *Go to next level* button."

Tactics rfl
