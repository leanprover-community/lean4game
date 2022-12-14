import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 15

Title "Oder"

Introduction
"
Das logische ODER `A ∨ B` (`\\or`) funktioniert ein wenig anders als das UND.

Wenn das Goal ein `∨` ist kann man mit `left` oder `right` entscheiden,
welche Seite man beweisen möchte.
"

Statement
    "Angenommen $A$ ist wahr, zeige $A \\lor (\\neg B))$"
    (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  left
  assumption

Hint (A : Prop) (B : Prop) (hA : A) : A ∨ (¬ B) =>
"Entscheide dich, `right` oder `left`?"

Message (A : Prop) (B : Prop) (hA : A) : ¬ B =>
"Sackgasse. Probier's nochmals."

Tactics left right assumption
