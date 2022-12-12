import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases

set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 11

Title "Genau dann wenn"

Introduction
"
Umgekehrt, wenn man eine Annahme `(h : A ↔ B)` hat, kann man auf verschiedene
Arten die Einzelteile `A → B` und `B → A` extrahieren.

- mit `rcases h` oder `rcases h with ⟨h₁, h₂⟩` teilt man die Annahme `h` auf. (Im zweiten Fall gibt
man explizit an, wie die neuen Annahmen heissen sollen, die Klammern sind `\\<` und `\\>`).

"
Statement
    (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  rcases h
  exact mp

Message (A : Prop) (B : Prop) : (A ↔ B) → A → B =>
"Angefangen mit `intro h` kannst du annehmen, dass `(h : A ↔ B)` wahr ist."

Conclusion
"
Anstatt
```
intro h
rcases h with ⟨h₁, h₂⟩
```
kann man direkt `intro ⟨h₁, h₂⟩` schreiben.
Wie du schon gesehen hast, sind diese Klammern `⟨⟩` Lean's Syntax für eine Struktur aus
mehreren Teilen.

"

Tactics intro apply rcases assumption







-- TODO: The new `cases` works differntly. There is also `cases'`
example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  cases h with
  | intro a b =>
    assumption

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  cases' h with a b
  assumption
