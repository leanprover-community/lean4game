import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 6
Title "Or, and the `left` and `right` tactics."

open MyNat

Introduction
"
`P ∨ Q` means \"$P$ or $Q$\". So to prove it, you
need to choose one of `P` or `Q`, and prove that one.
If `P ∨ Q` is your goal, then `left` changes this
goal to `P`, and `right` changes it to `Q`.
"
-- Note that you can take a wrong turn here. Let's
-- start with trying to prove $Q\\implies (P\\lor Q)$.
-- After the `intro`, one of `left` and `right` leads
-- to an impossible goal, the other to an easy finish.

Statement
"If $P$ and $Q$ are true/false statements, then $Q\\implies(P\\lor Q)$."
    (P Q : Prop) : Q → (P ∨ Q) := by
  Hint (hidden := true) "Let's start with an initial `intro` again."
  intro q
  Hint "Now you need to choose if you want to prove the `left` or `right` side of the goal."
  Branch
    left
    -- TODO: This message is also shown on the correct track. Need strict hints.
    -- Hint "That was an unfortunate choice, you entered a dead end that cannot be proved anymore.
    -- Hit \"Undo\"!"
  right
  exact q

NewTactic left right
NewDefinition Or

