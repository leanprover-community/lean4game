import Game.Metadata

World "TestWorld"
Level 1

Title "Test Level"

Introduction "This is a test level. There can be $\\textbf{LaTeX}$"

variable (x y : Nat)

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start \
        using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/-- The way to proof reflexivity. -/
TacticDoc rfl

/-- Commutativity on `ℕ` -/
TheoremDoc Nat.add_comm as "add_comm" in "ℕ"

/-- An equality -/
DefinitionDoc Eq as "equality" in "=="

/-- Addition -/
DefinitionDoc Add as "+"

NewDefinition Eq Add
NewTactic rw rfl
NewTheorem Nat.add_comm
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
