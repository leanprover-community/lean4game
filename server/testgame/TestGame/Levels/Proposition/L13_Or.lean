import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 13

Title "Und/Oder"

Introduction
"
Übung macht den Meister: Benutze alle vier Methoden mit UND und ODER
umzugehen um folgende Aussage zu beweisen.

|         | Und (`∧`)                | Oder (`∨`)              |
|---------|:-------------------------|:------------------------|
| Annahme | `rcases h with ⟨h₁, h₂⟩` | `rcases h with h \\| h` |
| Goal    | `constructor`            | `left`/`right`          |
"

-- Note: The other direction would need arguing by cases.

Statement
    "Angenommen $A \\lor (B \\land C)$ ist wahr, zeige dass
    $(A \\lor B) \\land (A \\lor C)$ wahr ist."
    (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  constructor
  rcases h with h | h
  left
  assumption
  rcases h with ⟨h₁, h₂⟩
  right
  assumption
  rcases h with h | h
  left
  assumption
  rcases h with ⟨h₁, h₂⟩
  right
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ B) ∧ (A ∨ C) =>
"Das `∧` in der Annahme kann mit `rcases h with ⟨h₁, h₂⟩` zerlegt werden."

Message (A : Prop) (B : Prop) (C : Prop) : (A ∨ B) ∧ (A ∨ C) =>
"Das `∧` im Goal kann mit `constructor` zerlegt werden."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) =>
"Das `∨` in der Annahme kann mit `rcases h with h | h` zerlegt werden."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) =>
"Das `∨` in der Annahme kann mit `rcases h with h | h` zerlegt werden."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ C) =>
"Das `∨` in der Annahme kann mit `rcases h with h | h` zerlegt werden."


Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ B) =>
"Das `∧` in der Annahme kann mit `rcases h with ⟨h₁, h₂⟩` zerlegt werden."

Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ C) =>
"Das `∧` in der Annahme kann mit `rcases h with ⟨h₁, h₂⟩` zerlegt werden."

-- TODO: Message nur Anhand der Annahmen?

Hint (A : Prop) (B : Prop) : A ∨ B =>
"`left` oder `right`?"

Tactics left right assumption constructor rcases
