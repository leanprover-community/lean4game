import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 8

Title "Implikation"

Introduction
"
Wenn das Goal von der Form `A → B` ist, kann man mit `intro hA` annehmen, dass `A` wahr ist
(i.e. erstellt eine Annahme `(hA : A)`)
und das Goal wird zu `B`.
"

Statement
    (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply f
  assumption

Tactics intro apply assumption
