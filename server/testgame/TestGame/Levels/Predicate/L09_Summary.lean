import TestGame.Metadata
import Mathlib.Tactic.PushNeg
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Predicate"
Level 9

Title "Zusammenfassung"

Introduction
"
Damit bist du am Ende der dritten Lektion angekommen.
Hier ein Überblick über alles was in diesem Kapitel eingeführt wurde und eine
Abschlussaufgabe.

## Notationen / Begriffe

|               | Beschreibung                |
|:--------------|:----------------------------|
| `ℕ`           | Die natürlichen Zahlen.     |
| `∃`           | Existential-Quantifier      |
| `∀`           | Forall-Quantifier           |
| `Even n`      | `n` ist gerade              |
| `Odd n`       | `n` ist ungerade            |


## Taktiken

|       | Taktik                    | Beispiel                                               |
|:------|:--------------------------|:-------------------------------------------------------|
| *11ᶜ* | `rw`                      | Umschreiben mit Gleichungen.                           |
| 12    | `ring`                    | Löst Gleichungen mit `+, -, *, ^`.                     |
| 13    | `unfold`                  | Setzt visuell die Bedeutung einer Definition ein.      |
| 14    | `use`                     | Um ein `∃` im Goal anzugehen.                          |
| *7ᶜ*  | `rcases h with ⟨x, hx⟩`   | Um ein `∃` in den Annahmen zu zerlegen.                |
| *8ᵇ*  | `intro`                   | Um ein `∀` im Goal anzugehen.                          |
| 15    | `push_neg`                | Für `¬∃` und `¬∀` im Goal.                             |

Als Abschlussübung kannst du folgende Äquivalenz zeigen:

"

Statement
    "TODO":
  True := by
  trivial

Conclusion ""

NewTactic push_neg intro use rw unfold ring
NewDefinition Even Odd
NewLemma not_even not_odd not_exists not_forall
