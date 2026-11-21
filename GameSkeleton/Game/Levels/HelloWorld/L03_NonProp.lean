import Game.Metadata

World "HelloWorld"
Level 3

Title "Non-Prop-Valued"

Introduction "This is a test level."

/-- level 3 -/
DefinitionDoc level3 as "level3"

-- TODO: name me
Statement level3 : Nat → Nat := by
  Hint "intro first!"
  intro x
  Hint "now apply!"
  apply x

Conclusion "Done!"

NewTactic intro apply
