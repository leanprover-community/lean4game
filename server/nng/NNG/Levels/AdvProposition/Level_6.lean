import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
--import Mathlib.Logic.Basic

Game "NNG"
World "AdvProposition"
Level 6
Title "Or, and the `left` and `right` tactics."

open MyNat

Introduction
"
`P ∨ Q` means \"$P$ or $Q$\". So to prove it, you
need to choose one of `P` or `Q`, and prove that one.
If `⊢ P ∨ Q` is your goal, then `left` changes this
goal to `⊢ P`, and `right` changes it to `⊢ Q`.
Note that you can take a wrong turn here. Let's
start with trying to prove $Q\\implies (P\\lor Q)$.
After the `intro`, one of `left` and `right` leads
to an impossible goal, the other to an easy finish.
"

Statement
"If $P$ and $Q$ are true/false statements, then
$$Q\\implies(P\\lor Q).$$ "
    (P Q : Prop) : Q → (P ∨ Q) := by
  intro q
  right
  assumption

NewTactic left right

Conclusion
"

"
