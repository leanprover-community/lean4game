import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 12

Title "Zusammenfassung"

Introduction
"
Damit bist du am Ende der zweiten Lektion angekommen.
Hier ein Überblick über alles was in diesem Kapitel eingeführt wurde und eine
Abschlussaufgabe.

## Notationen / Begriffe

|               | Beschreibung                                             |
|:--------------|:---------------------------------------------------------|
| →             | Eine Implikation.                                        |
| ↔             | Genau-dann-wenn / Äquivalenz.                            |
| `lemma`       | Ein Resultat mit einem Namen.                            |
| `theorem`     | Das gleiche wie ein Lemma.                               |
| `example`     | Wie ein Lemma aber ohne Namen (nicht weiter verwendbar.) |

## Taktiken

|     | Taktik                    | Beispiel                                               |
|:----|:--------------------------|:-------------------------------------------------------|
| 8   | `intro`                   | Für eine Implikation im Goal.                          |
| 9   | `revert`                  | Umkehrung von `intro`.                                 |
| 10  | `apply`                   | Wendet eine Implikation auf das Goal an.               |
| 10ᵇ | `apply`                   | Wendet ein Lemma an.                                   |
| 11  | `rw`                      | Umschreiben zweier äquivalenter Aussagen.              |
| 11ᵇ | `rw`                      | Benutzt ein Lemma, dessen Aussage eine Äquivalenz ist. |


Als Abschlussübung kannst du folgende Äquivalenz zeigen:
"

Statement imp_iff_not_or
"$A \\Rightarrow B$ ist äquivalent zu $\\neg A \\lor B$."
    (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  constructor
  apply not_or_of_imp
  intro h ha
  rcases h with h | h
  contradiction
  assumption

Hint (A : Prop) (B: Prop) : (A → B) ↔ ¬ A ∨ B =>
"Eine Äquivalenz im Goal geht man immer mit `constructor` an."

Hint (A : Prop) (B: Prop) : (A → B) → ¬ A ∨ B =>
"Diese Aussage hast du vorhin bereits als Lemma kennengelernt und angewendet."

Hint (A : Prop) (B: Prop) (h : A → B) : ¬ A ∨ B =>
"Diese Aussage hast du vorhin bereits als Lemma kennengelernt und angewendet."

Hint (A : Prop) (B: Prop) : ¬ A ∨ B → (A → B) =>
"Eine Implikation geht man fast immer mit `intro h` an."

Hint (A : Prop) (B: Prop) (h : ¬ A ∨ B) : (A → B) =>
"Nochmals `intro`."

Hint (A : Prop) (B: Prop) (h : ¬ A ∨ B) : (A → B) =>
"Das ODER in den Annahmen kannst du mit `rcases h with h | h` aufteilen."

Hint (A : Prop) (B: Prop) (h : ¬ A ∨ B) (ha : A) : B =>
"Das ODER in den Annahmen kannst du mit `rcases h with h | h` aufteilen."

Hint (A : Prop) (B: Prop) (ha : A) (ha' : ¬A) : B =>
"Findest du einen Widerspruch?"

Tactics rfl assumption trivial left right constructor rcases

Lemmas not_not not_or_of_imp
