import GameServer.Commands
import TestGame.MyNat
import TestGame.TacticDocs
import TestGame.LemmaDocs

Game "TestGame"

Title "The Natural Number Game"

Introduction
"This is a sad day for mathematics. While trying to find glorious new foundations for mathematics,
someone removed the law of excluded middle and the axiom of choice. Unsurprisingly,
everything collapsed. A brave rescue team managed to retrieve our precious axioms from the wreckage 
but now we need to rebuild all of mathematics from scratch.

As a beginning mathematics wizard, you've been tasked to rebuild the theory of natural numbers from 
the axioms that Giuseppe Peano found under the collapsed tower of number theory. You've been equipped
with a level 1 spell book. Good luck."

Conclusion
"There is nothing else so far. Thanks for rescuing natural numbers!"

World "w1"
World "w2"
World "w3"
World "v1"
World "v2"
World "v3"
World "v4"


Path TestWorld → w1 → w2 → w3
Path w1 → v1 → v2 → v3 → w3
Path v3 → v4