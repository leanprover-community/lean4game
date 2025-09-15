import Game.Metadata

World "TestWorld"
Level 1

Title "Test Level"

Introduction "This is a test level. There can be $\\textbf{LaTeX}$"

variable (x y : Nat)

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`.
  Single newlines are stripped."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
