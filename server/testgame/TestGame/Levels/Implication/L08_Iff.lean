import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 8

Title "Genau dann wenn"

Introduction
"
Nun schauen wir uns Option 1) an, die du schon von UND kennst:

1. Mit `h.mp` und `h.mpr` (oder `h.1` und `h.2`) kann man die einzelnen Implikationen
   direkt auswählen.

`h.mp` und `h.mpr` (oder `h.1` und `h.2`) sind die einzelnen Implikationen, und du kannst
mit denen ensprechend arbeiten. Insbesondere kannst du mit `apply h.mp` die Implikation
$A \\Rightarrow B$ anwenden, wenn das Goal $B$ ist.

*(PS: das `.mp` kommt von \"Modus Ponens\", ein Ausdruck as der Logik.)*
"

Statement
"Angenommen man hat $A \\iff B$ und $B \\Rightarrow C$, zeige $A \\Rightarrow C$."
    (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply h.mp
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) : A → C =>
"Fange wie immer mit `intro` an."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) (hA : A) : C =>
"Wie im Implikationen-Level kannst du nun `apply` verwenden."

Hint (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) (hA : A) : B =>
"Mit `apply h.mp` kannst du nun die Implikation `A → B` anwenden."

Conclusion "Im nächsten Level findest du die zweite Option."

Tactics apply assumption
