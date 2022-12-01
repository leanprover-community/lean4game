import TestGame.Metadata
import Mathlib

Game "TestGame"
World "TestWorld"
Level 14

Title "Oder"

Introduction
"
Das logische ODER `A ∨ B` (`\\or`) funktioniert
"

Statement
    (A B C : Prop) (h : (A ∨ B) ∨ C) : B ∨ (C ∨ A) := by
  cases h




Message (A : Prop) (B : Prop) : A ∧ (A → B) ↔ A ∧ B =>
"`↔` oder `∧` im Goal kann man mit `constructor` aufteilen."

-- if they don't use `intro ⟨_, _⟩`.
Message (A : Prop) (B : Prop) (h : A ∧ (A → B)) : A ∧ B =>
"Jetzt erst mal noch schnell die Annahme `A ∧ (A → B)` mit `rcases` aufteilen."

-- if they don't use `intro ⟨_, _⟩`.
Message (A : Prop) (B : Prop) (h : A ∧ B) : A ∧ (A → B) =>
"Jetzt erst mal noch schnell die Annahme `A ∧ B` mit `rcases` aufteilen."

Message (A : Prop) (B : Prop) (hA : A) (h : A → B) : A ∧ B =>
"Wieder in Einzelteile aufteilen..."

Message (A : Prop) (B : Prop) : A ∧ (A → B) =>
"Immer das gleiche ... noch mehr aufteilen."

Message (A : Prop) (B : Prop) (h₁: A) (h₂: B) : A → B =>
"Das ist jetzt vielleicht etwas verwirrend: Wir wollen die Implikation `A → B` zeigen,
wissen aber, dass `B` immer wahr ist (habe eine Annahme der Form `(hB : B)`).

Mit intro können wir einfach nochmal annehmen, dass `A` wahr ist. Es stört uns nicht,
dass wir das schon wissen und auch gar nicht brauchen. Damit müssen wir nur noch zeigen,
dass `B` wahr ist."

Hint (A : Prop) (B : Prop) (hA : A) (h : A → B) : B =>
"Sieht nach einem Fall für `apply` aus."


-- TODO


Tactics apply rcases
Tactics assumption
