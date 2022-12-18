import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 9

Title "Implikation"

Introduction
"
Wenn das Goal eine Implikation $A \\Rightarrow B$ ist, kann man mit
`intro hA` annehmen, dass $A$ wahr ist. Dann muss man $B$ beweisen.
"

Statement
    "Angenommen man weiss $A \\Rightarrow B \\Rightarrow C$, zeige dass $A \\Rightarrow C$."
    (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply f
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (f : A → B) (g : B → C) : A → C =>
"Mit `intro hA` kann man eine Implikation angehen."

Message (A : Prop) (B : Prop) (C : Prop) (hA : A) (f : A → B) (g : B → C) : C =>
"Jetzt ist es ein altbekanntes Spiel von `apply`-Anwendungen."


Tactics intro apply assumption
