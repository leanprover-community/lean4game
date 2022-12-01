import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

set_option tactic.hygienic false

Game "TestGame"
World "TestWorld"
Level 15

Title "Oder"

Introduction
"
Wenn man hingegen ein ODER - `(h : A ∨ B)` - in den Annahmen hat, kann man dieses
ähnlich wie beim UND mit `rcases h` aufteilen.

ABER! Beim UND `(h : A ∧ B)` hat man dann zwei neue Annahmen erhalten, und diese hat man mit
`rcases h with ⟨hA, hB⟩` benannt. Beim ODER `(h : A ∨ B)` kriegt man stattdessen zwei **Goals**
wo man annimmt, dass entweder die linke oder rechte Seite von `h` war ist.
Diese Annahme benennt man dann mit `rcases h with hA | hB`.
"

Statement and_or_imp
  "Benutze alle vier Methoden mit UND und ODER umzugehen um folgende Aussage zu beweisen."
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

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B ∨ (A → C)) (hA : A) : B ∨ (C ∧ A) =>
"Ein ODER in den Annahmen teilt man mit `rcases h with h₁ | h₂`. Der `|` signalisiert
dass `h₁` und `h2` die Namen der neuen Annahmen in den verschiedenen Fällen sind."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) (hA : A) : B ∨ (C ∧ A) =>
"Ein ODER im Goal kann mit `left` oder `right` angegangen werden."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) (hA : A) : B =>
"Ein UND in den Annahmen kann man mit `rcases h with ⟨h₁, h₂⟩` aufteilen.
Der Konstruktor `⟨⟩` signalisiert hier, dass dann nur ein Goal aber zwei neu benannte
Annahmen erhält."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) : C =>
"Sackgasse."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∧ B) : C ∧ A =>
"Hmmm..."

Message (A : Prop) (B : Prop) (C : Prop) (h : A → C) : C ∧ A =>
"Ein UND im Goal kann mit `constructor` aufgeteilt werden."

Tactics left right assumption constructor rcases apply
