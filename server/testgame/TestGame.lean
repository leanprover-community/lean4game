import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
import TestGame.Levels.Prime
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
Durch eine unvorhergesehene und nicht-kanonische Singularität in der Raumzeit
bist Du ausversehen in ein Paralleluniversum gestolpert. Wie es aussieht, gibt es kein zurück.
Richte Dich besser darauf ein, hier bleiben und Dich zurechtzufinden zu müssen.

Wie es aussieht, gibt es hier viele nette kleine Planeten. Alle bewohnbar, und bis zu
sieben Sonnenuntergänge täglich inklusive. Nur werden sie allesamt von Formalosophen bewohnt,
seltsamen Wesen mit ausgefallenen mathematischen Obsessionen. Und dummerweise hat sich
herumgesprochen, dass Du in Deinem früheren Universum Mathematiker warst. Du wirst hier
keine Ruhe finden, solange Du nicht lernst, ihren unablässigen Wissensdurst zu stillen.

Es gibt nur zwei Schwierigkeiten: Erstens haben die Formalosophen allem Anschein nach
überhaupt kein tieferes mathematisches Verständnis, und zweitens kommunizieren Sie
exklusiv in einem Dir fremden Dialekt. Zum Glück hat Robo mit Dir das Universum gewechselt.
Robo, das ist Dein kleiner SmartElf. Robo kann zwar auch keine Mathematik, aber es scheint,
er kann irgendetwas mit dem Formalosophendialekt anfangen.
"
Conclusion
"Fertig!"


Path Proposition → Implication → Predicate → Prime
Path Predicate → Contradiction → LeanStuff → SetTheory → SetTheory2 → SetFunction
Path SetTheory2 → Numbers

Path Module → Basis → Module2

Path Contradiction → Inequality → Induction → LeanStuff → Function → SetFunction

MakeGame
