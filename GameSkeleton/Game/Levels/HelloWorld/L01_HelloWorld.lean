import Game.Metadata

World "HelloWorld"
Level 1

Title "Hello Level"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides. There can be $\\textbf{LaTeX}$"

variable (x y : Nat)

Statement MyLevel1 (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start \
        using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "Maybe you should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  Hint (hidden := true) "Hidden Hint 1"
  Hint (hidden := true) "Hidden Hint 2"
  rw [g]

Conclusion "This last message appears if the level is solved."

NewDefinition Eq Add
NewTactic rw rfl
NewHiddenTactic simp
NewTheorem Nat.add_comm
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
