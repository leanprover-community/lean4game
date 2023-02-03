import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "SetFunction"
Level 1

Title "Abbildungen"

Introduction
"
Fortsetzung: Funktionen auf Mengen.

"

Statement
    "TODO"
    : True := by
  trivial

NewTactics rw
