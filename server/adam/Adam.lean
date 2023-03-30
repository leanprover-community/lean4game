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
# Game Over oder QED?

Willkommen zu unserem Prototyp eines Lean4-Lernspiels. Hier lernst du Computer-gestütztes
Beweisen. Das Interface ist anfangs etwas vereinfacht, der \"Editor Mode\" funktioniert aber
ziemlich gleich wie wenn du später Lean im VSCode benützt.

Rechts siehst du eine Übersicht der Welt dieses Spiels. Jeder Planet hat mehrere Levels,
die in Form von grauen Punkten dargestellt sind. Gelöste Levels werden dann grün.

Klicke auf die erste Welt \"Aussagenlogik 1\" um deine Reise zu starten.

### Spielstand

Dein Spielstand wird lokal in deinem Browser als \"site data\" gespeichert.
Solltest du diese löschen, verlierst du deinen Spielstand! Du kannst aber jederzeit jeden
Level spielen, auch wenn frühere Levels nicht grün sind.

(oft werden *Site data & Cookies* zusammen gelöscht).

### Funding

This game has been developed within the project
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/).
The project is based at Heinrich Heine University Düsseldorf and funded by Stiftung
Innovation in der Hochschullehre.

### Kontakt

Wenn du Bugs findest, schreib doch ein Email oder erstelle einen
[Issue auf Github](https://github.com/leanprover-community/lean4game/issues).

Jon Eugster, jon.eugster@hhu.de

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
