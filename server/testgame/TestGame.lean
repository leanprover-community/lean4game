import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
--import TestGame.Levels.Prime
import TestGame.Levels.Induction

import TestGame.Levels.LeanStuff
import TestGame.Levels.SetTheory
import TestGame.Levels.Function
import TestGame.Levels.SetFunction



Game "TestGame"
Title "Lean 4 game"
Introduction
"Work in progress.
"
Conclusion
"There is nothing else so far. Thanks for rescuing natural numbers!"


Path Proposition → Implication → Predicate → Contradiction → LeanStuff
--Path Predicate → Prime
Path Predicate → Induction → LeanStuff → Function → SetFunction

Path LeanStuff → SetTheory → SetFunction
