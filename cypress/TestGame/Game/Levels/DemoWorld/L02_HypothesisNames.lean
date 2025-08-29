import Game.Metadata

World "TestWorld"
Level 2

Title "Hypothesis Names"

Introduction "This is a test level."

Statement (x y z : Nat) (h : x = y) : x + z = y + z := by
  have g : x + z = y + z := by rw [h]
  Hint "You should use `{g}` now."
  exact g

Conclusion "Done!"

NewTactic exact «have»
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
