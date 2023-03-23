import TestGame.Metadata
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 1

Title "Intro"

Introduction
"
**Operationsleiter**: Sagt mal, könnt ihr mir hier weiterhelfen?
"

Statement (A B : Prop) (hb : B) : A → (A ∧ B) := by
  Hint "**Du**: Einen Moment, das ist eine Implikation (`\\to`),
  also `A` impliziert `A und B`, soweit so gut, also eine Tautologie.

  **Robo**: Du hast recht, eigentlich könnte man `tauto` sagen,
  aber das scheinen die hier tauto nicht zu verstehen.
  Implikationen kannst du aber mit `intro h` angehen."
  intro hA
  Hint "**Du**: Jetzt habe ich also angenommen, dass `A` wahr ist und muss `A ∧ B` zeigen,
  das kennen wir ja schon."
  constructor
  assumption
  assumption

Conclusion "Der Operationsleiter nickt bedacht."

NewTactic intro
DisabledTactic tauto
