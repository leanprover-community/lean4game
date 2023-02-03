import TestGame.Metadata
import Mathlib.Tactic.Ring

Game "TestGame"
World "Nat2"
Level 5

Title "Exists unique"

Introduction
"
TODO: Es existiert genau eine gerade Primzahl.

"

Statement "" : True := by
  trivial

Conclusion
"
"

NewTactics ring
