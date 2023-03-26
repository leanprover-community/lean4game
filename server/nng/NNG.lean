import GameServer.Commands

import NNG.Levels.Tutorial
import NNG.Levels.Addition
import NNG.Levels.Multiplication
import NNG.Levels.Power
import NNG.Levels.Function
import NNG.Levels.Proposition
import NNG.Levels.AdvProposition
import NNG.Levels.AdvAddition
import NNG.Levels.AdvMultiplication
import NNG.Levels.Inequality

Game "NNG"
Title "Natural Number Game"
Introduction
"
[intro text missing]

## Credits
* Content and Lean3-version: Kevin Buzzard, Mohammad Pedramfar
* Game Engine: Alexander Bentkamp, Jon Eugster, Patrick Massot
* Port to Lean 4: Chris Lovett

## Resources
* [Original Lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
* [Chris' translation to lean4](https://lovettsoftware.com/NaturalNumbers/TutorialWorld/Level1.lean.html)
"

Path Tutorial → Addition → Function → Proposition → AdvProposition → AdvAddition
Path AdvAddition → AdvMultiplication → Inequality
Path Addition → Multiplication → AdvMultiplication
Path Multiplication → Power

MakeGame