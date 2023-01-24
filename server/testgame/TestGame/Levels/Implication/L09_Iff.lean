import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases

Game "TestGame"
World "Implication"
Level 9

Title "Genau dann wenn"

Introduction
"
Und noch die letzte Option:

2. Mit `rcases h with ⟨h₁, h₂⟩` könnte man die Struktur `h` zerlegen und man erhält zwei
   separate Annahmen `(h₁ : A → B)` und `(h₂ : B → A)`

Als letzte Option kannst du `rcases h with ⟨h₁, h₂⟩` auch auf eine Annahme `(h : A ↔ B)`
anwenden, genau wie du dies bei einer Annahme `(h' : A ∧ B)` gemacht hast.
"
Statement
"Angenommen man hat $A \\iff B$ und $B \\Rightarrow C$, zeige $A \\Rightarrow C$."
    (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  rcases h
  assumption

HiddenHint (A : Prop) (B : Prop) : (A ↔ B) → A → B =>
"Angefangen mit `intro h` kannst du annehmen, dass `(h : A ↔ B)` wahr ist."

HiddenHint (A : Prop) (B : Prop) (h : A ↔ B) : A → B =>
"Mit `rcases h with ⟨h₁, h₂⟩` kannst du jetzt die Annahme `(h : A ↔ B)` zerlegen."


Conclusion
"
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
