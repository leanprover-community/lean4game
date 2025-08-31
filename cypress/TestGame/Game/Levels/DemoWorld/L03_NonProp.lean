import Game.Metadata

World "TestWorld"
Level 3

Title "Non-Prop-Valued"

Introduction "This is a test level."

-- TODO: name me
Statement : Nat → Nat := by
  Hint "intro first!"
  intro x
  Hint "now apply!"
  apply x

Conclusion "Done!"

NewTactic intro apply
