import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases

Game "TestGame"
World "Implication"
Level 8

Title "Genau dann wenn"

Introduction
"
Als zweite Option, kann man eine Annahme `(h : A ↔ B)` in zwei neue Annahmen
`(h₁ : A → B)` und `(h₂ : B → A)` aufteilen.

2.) Mit `rcases h` teilt man die Annahme `h` auf.

(Mit `rcases h with ⟨h₁, h₂⟩` (`\\<`, `\\>`) kann man zudem die neuen Annahmen benennen.)

"
Statement
    "Angenommen man hat $A \\iff B$ und $B \\Rightarrow C$, zeige $A \\Rightarrow C$."
    (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  rcases h
  assumption

Message (A : Prop) (B : Prop) : (A ↔ B) → A → B =>
"Angefangen mit `intro h` kannst du annehmen, dass `(h : A ↔ B)` wahr ist."

Message (A : Prop) (B : Prop) (h : A ↔ B): A → B =>
"Mit `rcases h with ⟨h₁, h₂⟩` kannst du jetzt die Annahme `(h : A ↔ B)` zerlegen."


Conclusion
"
Note: In der Mathematik definieren wir oft Strukturen als Tupels, z.B. \"Sei (G, +) eine Gruppe\".
In Lean brauchen wir dafür immer die Klammern von oben: `⟨_, _⟩`.
"

Tactics intro apply rcases assumption

-- -- TODO: The new `cases` works differntly. There is also `cases'`
-- example (A B : Prop) : (A ↔ B) → (A → B) := by
--   intro h
--   cases h with
--   | intro a b =>
--     assumption

-- example (A B : Prop) : (A ↔ B) → (A → B) := by
--   intro h
--   cases' h with a b
--   assumption
