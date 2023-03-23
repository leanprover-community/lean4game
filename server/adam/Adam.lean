import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
-- import TestGame.Levels.Prime
import TestGame.Levels.Sum
-- import TestGame.Levels.Induction

import TestGame.Levels.Numbers
import TestGame.Levels.Inequality

import TestGame.Levels.Lean
import TestGame.Levels.SetTheory
import TestGame.Levels.Function
import TestGame.Levels.SetFunction
import TestGame.Levels.LinearAlgebra



Game "TestGame"
Title "Lean 4 game"
Introduction
"
"

Conclusion
"Fertig!"


Path Proposition → Implication → Predicate → Predicate → Contradiction → Sum → Lean
Path Predicate → Inequality → Sum
-- Path Inequality → Prime
-- Path Sum → Inequality -- → Induction

Path Lean → SetTheory → SetTheory2 → SetFunction → Module
Path Lean → Function → SetFunction


Path SetTheory2 → Numbers
Path Module → Basis → Module2

MakeGame
