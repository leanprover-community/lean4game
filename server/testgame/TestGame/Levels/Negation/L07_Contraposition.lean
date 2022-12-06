import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose

Game "TestGame"
World "Contradiction"
Level 7

Title "Kontraposition"

Introduction
"
Im Gegensatz zum Widerspruch, wo
"

Statement
  "Ein Widerspruch impliziert alles."
    (A B : Prop) (h : ¬ B → ¬ A) (hA : A) : B := by
  revert hA
  contrapose
  assumption

Tactics contradiction
