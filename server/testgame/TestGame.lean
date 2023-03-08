import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
import TestGame.Levels.Prime
import TestGame.Levels.Sum
import TestGame.Levels.Induction

import TestGame.Levels.Numbers
import TestGame.Levels.Inequality

import TestGame.Levels.LeanStuff
import TestGame.Levels.SetTheory
import TestGame.Levels.Function
import TestGame.Levels.SetFunction
import TestGame.Levels.LinearAlgebra



Game "TestGame"
Title "Lean 4 game"
Introduction
"
TODO
"

Conclusion
"Fertig!"


Path Proposition → Implication → Predicate
Path Predicate → Contradiction → Sum → LeanStuff
Path LeanStuff → SetTheory → SetTheory2 → SetFunction

Path Predicate → Prime → Induction
Path Sum → Inequality → Induction
Path Inequality → LeanStuff

Path SetTheory2 → Numbers
Path Module → Basis → Module2
Path LeanStuff → Function → SetFunction

MakeGame
