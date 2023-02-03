import TestGame.Metadata
import Mathlib.Tactic.Ring

Game "TestGame"
World "Nat2"
Level 3

Title "Primzahlen"

Introduction
"
TODO: Primzahl

"

Statement "" : True := by
  trivial

Conclusion
"
"

NewTactics ring
