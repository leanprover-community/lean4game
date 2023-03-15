import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 6

Title "Contradiction"

Introduction
"
**Du**: Sag mal Robo, das hätte ich aber auch als Widerspruch anstatt Kontraposition
beweisen können?

**Robo**: Klar. `contrapose` ist eine Kontraposition, `by_contra` ein Widerspruchsbeweis.
Probiers doch einfach!
In diesem Kapitel hast du also folgende Taktiken kennengelernt:


Als Vergleich zwischen Beweisen \"per Widerspruch\"
und \"per Kontraposition\", beweise die Gleiche Aufgabe indem
du mit `by_contra` einen Widerspruch suchst.
"

Statement (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  Hint "**Robo**: Fang diesmal mit `by_contra g` an!"
  by_contra g
  Hint "**Robo**: Jetzt würde ich einen Widerspruch zu `Odd (n ^ 2)` führen."
  Hint "**Robo**: Also `suffices g : ¬ Odd (n ^ 2)`."
  suffices d : ¬ Odd (n ^ 2)
  contradiction
  rw [not_odd] at *
  apply even_square
  assumption

DisabledTactic contrapose revert

Conclusion "**Robo**: Bravo! Hier nochmals ein Überblick, was wir jetzt alles auf diesem
Mond gelernt haben:

|       | Taktik          | Beispiel                                               |
|:------|:----------------|:-------------------------------------------------------|
| 177   | `have`          | Zwischenresultat annehmen.                             |
| 18    | `suffices`      | Zwischenresultat annehmen.                             |
| 19    | `by_contra`     | Widerspruch. (startet einen Widerspruch)               |
| *3*   | `contradiction` | *(Schliesst einen Widerspruchsbeweis)*                 |
| 20    | `contrapose`    | Kontraposition.                                        |
| *9*   | `revert`        | Nützlich um danach `contrapose` anzuwenden.            |
"
