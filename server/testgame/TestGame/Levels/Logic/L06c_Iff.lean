import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 12

Title "Genau dann wenn"

Introduction
"
Wenn man eine Annahme `(h : A ↔ B)` hat, kann man auch davon die beiden einzelnen
Implikationen $\\textrm{mp} : A \\Rightarrow B$ und $\\textrm{mpr} : B \\Rightarrow A$
brauchen.

Dazu gibt es zwei Methoden:

1.) `h.mp` (oder `h.1`) und `h.mpr` (oder `h.2`) sind direkt die einzelnen Richtungen.
Man kann also z.B. mit `apply h.mp` die Implikation `A → B` auf ein Goal `B` anwenden.

(PS: das `.mp` kommt von \"Modus Ponens\".)
"

Statement
    "Angenommen man hat $A \\iff B$ und $B \\Rightarrow C$, zeige $A \\Rightarrow C$."
    (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply h.mp
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) : A → C =>
"Zuerst kannst du wieder `intro` benützen um die Implikation anzugehen."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) (hA : A) : C =>
"Der nächste Schritt kommt auch noch aus dem Implikationen-Level."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ↔ B) (g : B → C) (hA : A) : B =>
"Mit `apply h.mp` kannst du nun die Implikation `A → B` anwenden."

Conclusion "Im nächsten Level findest du die zweite Option."

Tactics apply assumption
