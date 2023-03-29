import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 13

Title "Zusammenfassung"

Introduction
"
**Operationsleiter**: Damit endet unsere Führung langsam. Bevor ihr weitergeht
habe ich noch ein Problem, an dem ich mir die Zähne ausbeisse. Wir haben die
Herleitung eines unserer Programme `imp_iff_not_or` verloren, und wissen nicht mehr
ob es einwandfrei funktioniert.

**Du**: Nah gut, mal sehen. Robo, was hab ich denn alles hier gelernt?

**Robo**: Hier ist die Übersicht:

## Notationen / Begriffe

|               | Beschreibung                                             |
|:--------------|:---------------------------------------------------------|
| →             | Eine Implikation.                                        |
| ↔             | Genau-dann-wenn / Äquivalenz.                            |

## Taktiken

|     | Taktik                    | Beispiel                                               |
|:----|:--------------------------|:-------------------------------------------------------|
| 8   | `intro`                   | Für eine Implikation im Goal.                          |
| 9   | `revert`                  | Umkehrung von `intro`.                                 |
| 10  | `apply`                   | Wendet eine Implikation auf das Goal an.               |
| 10ᵇ | `apply`                   | Wendet ein Lemma an.                                   |
| 11  | `by_cases`                | Fallunterscheidung `P` und `¬P`                        |
| 12  | `rw`                      | Umschreiben zweier äquivalenter Aussagen.              |
| 12ᵇ | `rw`                      | Benutzt ein Lemma, dessen Aussage eine Äquivalenz ist. |
"

Statement imp_iff_not_or (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  constructor
  Hint "**Du**: Das sieht kompliziert aus…

  **Robo** *(flüsternd)*: Ja, aber die Richtung kennst du ja schon also Lemma,
  wend doch einfach das an."
  apply not_or_of_imp
  Hint "**Du**: Gibt es für die Gegenrichtung auch ein Lemma?

  **Robo**: Leider nicht. Da musst du manuell ran."
  Hint (hidden := true) "**Robo**: Na Implikationen fangst du immer mit `intro` an."
  intro h
  intro ha
  Hint (hidden := true) "**Robo**: Ich wür mal die Annahme `h` mit `rcases` aufteilen."
  rcases h with h | h
  contradiction
  assumption

DisabledTactic tauto

Conclusion "**Operationsleiter**: Damit gehen unsere Wege auseinander. Da fällt mir ein, seit
ihr auf dem Weg zu unserem Schwestermond?

**Du**: Könnten wir sein…

**Operationsleiter**: Ich hab hier einen Brief für *Evenine*, könntet ihr diesen mit euch führen?

**Du**: Klar! Robo, halt den mal.

Robo nimmt den Brief und lässt ihn irgendwo in seinem Innern verschwinden. Dabei bemerkt er
den besorgten Blick des Operationsleiters.

**Robo**: Keine Angst, ich verdaue nichts!"
