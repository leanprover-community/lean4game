import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib

Game "TestGame"
World "Implication"
Level 11

Title "by_cases"

Introduction
"
**Du**: Sagt mal, hätte ich da nicht auch einfach zwei Fälle anschauen können:
Wenn `A` wahr ist, beweis ich die rechte Seite, sonst die Linke.

**Robo**: Tatsächlich, `by_cases h : A` würde genau das machen!
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint (hidden := true) "**Du**: Wie?

  **Robo**: Also `by_cases h : A` erstellt zwei Goals. Im ersten hast Du `(h : A)` zur
  Verfügung, im zweiten `(h : ¬ A)`."
  by_cases h : A
  Hint "**Du**: "
  right
  assumption
  left
  assumption

Conclusion
"
**Du**: Das kann noch ganz nützlich sein.
"

NewTactic by_cases
DisabledTactic tauto
