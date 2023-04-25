import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 9
Title "a big maze."

open MyNat

Introduction
"
In Lean3 there was a tactic `cc` which stands for \"congruence closure\"
which could solve all these mazes automatically. Currently this tactic has
not been ported to Lean4, but it will eventually be available!

For now, you can try to do this final level manually to apprechiate the use of such
automatisation ;)
"
-- TODO:
-- "Lean's "congruence closure" tactic `cc` is good at mazes. You might want to try it now.
-- Perhaps I should have mentioned it earlier."

Statement
"There is a way through the following maze."
    (A B C D E F G H I J K L : Prop)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
    (f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
    (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L) : A → L := by
  Hint (hidden := true) "You should, once again, start with `intro a`."
  intro a
  Hint "Use a mixture of `apply` and `have` calls to find your way through the maze."
  apply f15
  apply f11
  apply f9
  apply f8
  apply f5
  apply f2
  apply f1
  exact a

-- TODO: Once `cc` is implemented,
-- NewTactic cc

Conclusion
"
Now move onto advanced proposition world, where you will see
how to prove goals such as `P ∧ Q` ($P$ and $Q$), `P ∨ Q` ($P$ or $Q$),
`P ↔ Q` ($P\\iff Q$).
You will need to learn five more tactics: `constructor`, `rcases`,
`left`, `right`, and `exfalso`,
but they are all straightforward, and furthermore they are
essentially the last tactics you
need to learn in order to complete all the levels of the Natural Number Game,
including all the 17 levels of Inequality World.
"
