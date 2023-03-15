import TestGame.Metadata

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
Level 3

Title "Arithmetische Summe"

Introduction
"
**Du**: Wie werden solche Meisterwerke eigentlich gebaut?

Da zeigt eure Begleitung auf eine kleine Steinplatte neben dem Eingang,
auf der eien Beschreibung gekritzelt ist.

**Robo**: Das ist wohl der bekannte arithmetische Turm von Indu, über den hab ich schon
einmal Daten verarbeitet. Und die antwort auf deine Frage: Vermutlich ein Stein nach
dem anderen.
"

open BigOperators

Statement arithmetic_sum
    "$2 \\cdot \\sum_{i = 0}^n i = n \\cdot (n + 1)$."
    (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  Hint "**Du**: Klar, die werden ja nicht oben anfangen mit bauen. Sag mal,
  wie zeige ich denn die arithmetische Summe, die hier gekritzelt steht?
  Ich würde gerne Induktion über $n$ anwenden.

  **Robo**: Ja dann ist's einfach `induction n`, ist doch logisch!"
  induction n
  Hint "**Du**: Zuerst den Induktionsanfang…

  **Robo**: Diesen kannst du oft mit `simp` abkürzen!"
  simp
  Hint "**Robo**: Jetzt im Induktionsschritt: Bei Induktion über endlichen Summen willst du
  immer mit `rw [Fin.sum_univ_castSucc]` anfangen" -- :

  -- $$\\sum_\{i=0}^n a_i = \\sum_{i=0}^\{n-1} a_i + a_n$$"
  rw [Fin.sum_univ_castSucc]
  -- TODO: Bug. Dieser Hint wird nicht angezeigt.
  Hint "**Du**: Oh das sieht jetz aber kompliziert aus…

  **Robo**: Da musst du etwas drüber hinweg lesen. Am besten machst du kurz `simp`,
  dann sieht's schon wieder besser aus."
  simp
  Hint "**Du**: Was bedeutet eigentlich der kleine Pfeil `↑`?

  **Robo**: Das ist eine *Coersion*. Sowas wie wenn man eine natürliche Zahl als Integer anschaut,
  also die natürliche Abbildung `ℕ ↪ ℤ`. Oder hier, wenn ein Element `x : Fin n` stattdessen als
  Element in `(↑x : ℕ)` angeschaut wird.

  **Robo**: Übrigens, um die Induktionshypothese anzuwenden brauchst du zuerst das Lemma
  `mul_add`."
  rw [mul_add]
  Hint "**Du**: Und wie wende ich jetzt die Induktionshypothese an?

  **Robo mit `rw` wie jede andere Annahme auch."
  rw [n_ih]
  Hint "**Robo**: Jetzt musst du noch kurz `rw [Nat.succ_eq_add_one]` anwenden.

  **Du**: Aber wieso?

  **Robo**: Naja, `ring` ist jetzt auch noch nicht so stark, und erkennt nicht dass `n.succ`
  und `n + 1` das gleiche sind.

  **Du**: Aber das könnte man doch ändern, oder?

  **Robo**: Vielleicht wenn wir einmal einem Techniker begegnen, der mir ein Update
  einspielen kann…"
  Branch
    ring_nf
    Hint "**Robo**: Wie gesagt, brauch doch `rw [Nat.succ_eq_add_one]` als Fix für meine
    kleinen Maken."
  rw [Nat.succ_eq_add_one]
  ring

NewTactic induction
NewLemma Fin.sum_univ_castSucc Nat.succ_eq_add_one mul_add add_mul

Conclusion "Du schaust dich um und bewunderst das Tal in dem hunderte, wenn nicht tausende,
Steintürme in allen Formen und Höhen stehen."
