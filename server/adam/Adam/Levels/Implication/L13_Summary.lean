import Adam.Metadata

import Adam.Options.MathlibPart

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 13

Title "Zusammenfassung"

Introduction
"
**Operationsleiter**: Ihr habt mir wirklich so geholfen!  Hier ist das letzte Problem.  Das habe ich von meinem Vorgänger geerbt.  Er hat behauptet, wenn wir das lösen können, dann läuft hier wieder alles.  Aber es sah mir immer viel zu schwierig aus, um es überhaupt zu versuchen. Wollt Ihr es einmal probieren?

**Du**: Klar, zeig her!  Robo, kannst du mir vielleicht auch noch einmal so eine nette Zusammenfassung anzeigen, was ich theoretisch in den letzten fünf Minuten gelernt habe?

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
  Hint "**Du** *(flüsternd)*: Ist das nicht die Definition von `→`?

  **Robo** *(flüsternd)*: Könnte man so sehen.  Aber auf Leansch ist das bloß eine Äquivalenz.
  So oder so kennst du ja eine Richtung schon als Lemma.
  Also wende das doch einfach an."
  apply not_or_of_imp
  Hint "**Du**: Gibt es für die Gegenrichtung auch ein Lemma?

  **Robo**: Leider nicht. Da musst du manuell ran."
  Hint (hidden := true) "**Robo**: Na Implikationen gehst du immer mit `intro` an."
  intro h
  intro ha
  Hint (hidden := true) "**Robo**: Ich würde mal die Annahme `h` mit `rcases` aufteilen."
  rcases h with h | h
  contradiction
  assumption

DisabledTactic tauto

Conclusion "**Operationsleiter**: Das ist ja fantastisch!  Tausend Dank!  Dann will ich Euch auch gar nicht länger aufhalten.
Ihr wollt bestimmt weiter zu Quantus, unserem Schestermond, oder?

**Du**: Ehm, vielleicht …

**Operationsleiter**: Dann habe ich noch eine letzte Bitte. Ich habe hier noch ein Päckchen für die Königin von Quantus!  Auch schon von meinem Vorgänger geerbt. Die Post will es nicht annehmen, weil ich die Adresse nicht weiß.  Könntet Ihr es vielleicht zu ihr mitnehmen?

**Du**: Klar! Robo, halt mal.

Robo nimmt das Päckchen und lässt es irgendwo in seinem Innern verschwinden.
Der Operationsleiter sieht ihn entgeistert an.

**Robo**: Keine Angst, ich verdaue nichts!"
