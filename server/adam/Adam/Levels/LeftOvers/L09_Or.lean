import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 9

Title "Oder"

Introduction
"
Übung macht den Meister... Benutze alle vier Methoden mit UND und ODER
umzugehen um folgende Aussage zu beweisen.

|         | Und                      | Oder                      |
|---------|:-------------------------|:--------------------------|
| Annahme | `rcases h with ⟨h₁, h₂⟩` | `rcases h with h₁ \\| h₂` |
| Goal    | `constructor`            | `left`/`right`            |
"

Statement and_or_imp
    "Angenommen $(A \\land B) \\lor (A \\Rightarrow C)$ und $A$ sind wahr, zeige dass
    $B \\lor (C \\land A)$ wahr ist."
    (A B C : Prop) (h : (A ∧ B) ∨ (A → C)) (hA : A) : (B ∨ (C ∧ A)) := by
  rcases h with h₁ | h₂
  left
  rcases h₁ with ⟨x, y⟩
  assumption
  right
  constructor
  apply h₂
  assumption
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B ∨ (A → C)) (hA : A) : B ∨ (C ∧ A) =>
"Ein ODER in den Annahmen teilt man mit `rcases h with h₁ | h₂`."

-- If starting with `left`.
Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B ∨ (A → C)) : B =>
"Da kommst du nicht mehr weiter..."

-- If starting with `right`.
Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B ∨ (A → C)) : (C ∧ A) =>
"Da kommst du nicht mehr weiter..."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) (hA : A) : B ∨ (C ∧ A) =>
"`left` oder `right`?"

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : B) (hA : A) : B ∨ (C ∧ A) =>
"`left` oder `right`?"

Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) (hA : A) : B ∨ (C ∧ A) =>
"Ein UND in den Annahmen kann man mit `rcases h with ⟨h₁, h₂⟩` aufteilen."

Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) (hA : A) : B =>
"Ein UND in den Annahmen kann man mit `rcases h with ⟨h₁, h₂⟩` aufteilen."

Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) : C =>
"Sackgasse."

Hint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) : C ∧ A =>
"Hmmm..."

Hint (A : Prop) (B : Prop) (C : Prop) (h : A → C) : C ∧ A =>
"Ein UND im Goal kann mit `constructor` aufgeteilt werden."

NewTactic left right assumption constructor rcases
