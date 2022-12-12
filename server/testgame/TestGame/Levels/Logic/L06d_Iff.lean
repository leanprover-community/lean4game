import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 12

Title "Genau dann wenn"

Introduction
"
Man kann auch die einzelnen Richtungen benützen, ohne `h` selber zu verändern:

- `h.1` und `h.2` sind direkt die einzelnen Richtungen. Man kann also z.B. mit `apply h.1` die
Implikation `A → B` auf ein Goal `B` anwenden.
- `h.mp` und `h.mpr` sind die bevorzugten Namen anstatt `.1` und `.2`. \"mp\" kommt von
\"Modus Ponens\", aber das ist hier irrelevant.
"

Statement
    "
    Benütze nur `apply` und `assumption` um das gleiche Resultat zu zeigen.
    "
    (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply h.mp
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) (hA : A) : B =>
"Mit `apply h.mp` kannst du nun die Implikation `A → B` anwenden."

Tactics apply
Tactics assumption
