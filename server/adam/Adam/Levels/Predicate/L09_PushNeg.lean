import TestGame.Metadata
import Mathlib.Tactic.PushNeg
import Mathlib

import Mathlib.Algebra.Parity

import TestGame.ToBePorted

Game "TestGame"
World "Predicate"
Level 9

Title "PushNeg"

Introduction
"
Das Dorf von *Oddeus* scheint stärker befestigt zu sein, all jenes von *Evenine*. Ihr kommt
and eine Wand aus Dornenranken. Beim Eingang steht eine Wache, die auch zuruft:

"

-- Zum Schluss, immer wenn man irgendwo eine Verneinung `¬∃` oder `¬∀` sieht (`\\not`), kann man
-- mit `push_neg` das `¬` durch den Quantor hindurchschieben.

-- Das braucht intern die Lemmas

-- - `not_exists (A : Prop) : ¬ (∃ x, A) ↔ ∀x, (¬A)`
-- - `not_forall (A : Prop) : ¬ (∀ x, A) ↔ ∃x, (¬A)`

-- (welche man auch mit `rw` explizit benutzen könnte.)

open Nat

Statement : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  Hint "**Du**: Also ich kann mal das `¬` durch die Quantifier hindurchschieben.

  **Robo**: `push_neg` macht genau das!

  **Robo**: Intern braucht das zwei Lemmas

  ```
  not_exists (A : Prop) : ¬ (∃ x, A) ↔ ∀x, (¬A)
  not_forall (A : Prop) : ¬ (∀ x, A) ↔ ∃x, (¬A)
  ```
  die du natürlich auch mit `rw` gebrauchen könntest."
  Branch
    unfold Odd
    push_neg
    Hint "**Robo**: Der Weg ist etwas schwieriger. Ich würde nochmals zurück und schauen,
    dass du irgendwann `¬Odd` kriegst, was du dann mit `rw [←even_iff_not_odd]`
    zu `Even` umwandeln.
    kannst."
  push_neg
  intro n
  Hint "**Robo**: Welche Zahl du jetzt mit `use` brauchst, danach wirst du vermutlich das
  Lemma `←even_iff_not_odd` brauchen.

  **Du**: Könnte ich jetzt schon `rw [←even_iff_not_odd]` machen?

  **Robo**: Ne, `rw` kann nicht innerhalb von Quantifiern umschreiben.

  **Du**: Aber wie würde ich das machen?

  **Robo**: Zeig ich dir später, die Wache wird schon ganz ungeduldig!
  Im Moment würde ich zuerst mit `use` eine richtige Zahl angeben, und danach umschreiben."
  Branch
    use n + 2
    Hint "**Robo**: Gute Wahl! Jetzt kannst du `←even_iff_not_odd` verwenden."
  Branch
    use n + 4
    Hint "**Robo**: Gute Wahl! Jetzt kannst du `←even_iff_not_odd` verwenden."
  use n
  Hint "**Robo**: Gute Wahl! Jetzt kannst du `←even_iff_not_odd` verwenden."
  rw [←even_iff_not_odd]
  unfold Even
  use n
  --ring

Conclusion "Damit werdet ihr eingelassen.

**Robo**: Entweder wir suchen direkt diesen *Oddeus*, oder wir schauen uns einmal um. Die Wahl
ist deine!

**Du**: Kannst du mir nochmals einen Überblick geben, was wir gelernt haben?

**Robo**:

|               | Beschreibung                |
|:--------------|:----------------------------|
| `ℕ`           | Die natürlichen Zahlen.     |
| `∃`           | Existential-Quantifier      |
| `∀`           | Forall-Quantifier           |
| `Even n`      | `n` ist gerade              |
| `Odd n`       | `n` ist ungerade            |

|       | Taktik                    | Beispiel                                               |
|:------|:--------------------------|:-------------------------------------------------------|
| *12ᶜ* | `rw`                      | Umschreiben mit Gleichungen.                           |
| 13    | `ring`                    | Löst Gleichungen mit `+, -, *, ^`.                     |
| 14    | `unfold`                  | Setzt visuell die Bedeutung einer Definition ein.      |
| 15    | `use`                     | Um ein `∃` im Goal anzugehen.                          |
| *7ᶜ*  | `rcases h with ⟨x, hx⟩`   | Um ein `∃` in den Annahmen zu zerlegen.                |
| *8ᵇ*  | `intro`                   | Um ein `∀` im Goal anzugehen.                          |
| 16    | `push_neg`                | Für `¬∃` und `¬∀` im Goal.                             |

"

NewTactic push_neg
NewLemma Nat.even_iff_not_odd Nat.odd_iff_not_even not_exists not_forall
