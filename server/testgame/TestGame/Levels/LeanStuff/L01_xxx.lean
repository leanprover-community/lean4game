import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 1

Title ""

Introduction
"
Dieses Kapitel führt ein paar Lean-spezifische Sachen ein, die du wissen solltest.

Mathematisch haben diese Sachen keinen Inhalt, aber es ist wichtig, dass du etwas
verstehst wie Lean manche Sachen macht.


- Implizite und explizite Argumente.
- Types

"

open Set

Statement
    "TODO" : True := by
  trivial

Tactics rw
