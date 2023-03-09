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

Statement "" (A B : Prop) (hb : B) : A → (A ∧ B) := by
  intro hA
  constructor
  assumption
  assumption

NewTactic intro
DisabledTactic tauto

Hint (A : Prop) (B : Prop) (hb : B) : A → (A ∧ B) =>
"**Du**: Einen Moment, das ist eine Implikation (`\\to`),
also `A` impliziert `A und B`, soweit so gut, also eine Tautologie.

**Robo**: Die scheinen hier `tauto` auch nicht zu verstehen.
Implikationen kannst du aber mit `intro h` angehen."

Hint (A : Prop) (B : Prop) (ha : A) (hb : B) : (A ∧ B) =>
"**Du**: Jetzt habe ich also angenommen, dass `A` wahr ist und muss `A ∧ B` zeigen,
das kennen wir ja schon."

Conclusion "Der Operationsleiter nickt bedacht."
