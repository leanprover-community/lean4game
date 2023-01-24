import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
--import TestGame.Levels.Prime
import TestGame.Levels.Induction

Game "TestGame"

Title "Lean 4 game"

Introduction
"Work in progress.
"

Conclusion
"There is nothing else so far. Thanks for rescuing natural numbers!"


Path Proposition → Implication → Predicate → Contradiction
--Path Predicate → Prime
Path Predicate → Induction
