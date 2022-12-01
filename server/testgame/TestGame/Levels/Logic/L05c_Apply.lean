import TestGame.Metadata

Game "TestGame"
World "TestWorld"
Level 8

Title "Implikation"

Introduction
"
Wenn das Goal von der Form `A → B` ist, kann man mit `intro` annehmen, dass `A` wahr ist
und das Goal wird zu `B`.
"

Statement
    (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply f
  assumption

Tactics intro apply assumption
