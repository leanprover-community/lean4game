import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Contradiction"
Level 6

Title "Widerspruch"

Introduction
"
"


Statement
    (A : Prop) : A := by
  pushNeg


Tactics contradiction
