import Adam.Metadata

import Adam.Levels.Proposition
import Adam.Levels.Implication
import Adam.Levels.Predicate
import Adam.Levels.Contradiction
-- import Adam.Levels.Prime
import Adam.Levels.Sum
-- import Adam.Levels.Induction

import Adam.Levels.Numbers
import Adam.Levels.Inequality

import Adam.Levels.Lean
import Adam.Levels.SetTheory
import Adam.Levels.Function
import Adam.Levels.SetFunction
import Adam.Levels.LinearAlgebra



Game "Adam"
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
