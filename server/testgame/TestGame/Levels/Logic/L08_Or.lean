import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 14

Title "Oder"

Introduction
"
Das logische ODER `A ∨ B` (`\\or`) funktioniert ein wenig anders als das UND.

Wenn das Goal ein `∨` ist kann man mit `left` oder `right` entscheiden,
welche Seite man beweisen möchte.
"

Statement (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  left
  assumption

Tactics left right assumption
