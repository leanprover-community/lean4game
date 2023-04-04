import Adam.Metadata

import Adam.ToBePorted
import Adam.Options.MathlibPart

import Adam.Options.ArithSum

Game "Adam"
World "Sum"
Level 6

set_option tactic.hygienic false

Title "Zusammenfassung"

Introduction
"
**Du**: Robo gib mir nochmals eine Übersicht, bitte.

**Robo**: Aber klar:

|                      | Beschreibung                              |
|:---------------------|:------------------------------------------|
| `Fin n`              | Ist ein Typ mit Zahlen $0, \\ldots, n-1$. |
| `∑ (i : Fin n), a i` | $\\sum_{i=0}^{n-1} a_i$                   |
| `↑i`                 | Eine Coersion, z.B. `Fin n → ℕ`.          |

und

|    | Taktik                    | Beispiel                             |
|:---|:--------------------------|:-------------------------------------|
| 21 | `simp`                    | Simplifikation.                      |
| 22 | `induction n`             | Induktion über $n$                   |

Da löst sich aus der Steinlandschaft plötzlich ein grosser Steingolem. Er schaut euch
bedrohlich an und fragt in tiefer Stimme:
"

open Fin

open BigOperators

Statement (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  Hint "**Du**: Gulp. Naja das wird schon klappen. Also man fängt wieder mit Induktion an…"
  induction m
  Hint "**Du**: Also den Induktionsanfang kann man einfach zeigen…"
  simp
  Hint (hidden := true) "**Robo**: Und jetzt wieder `rw [sum_univ_castSucc]` und `simp` um vorwärts zu
  kommen!"
  rw [Fin.sum_univ_castSucc]
  simp
  Hint "**Robo**: Siehst du die Induktionshypothese hier drin?"
  rw [n_ih]
  Hint "**Du**: Ok, damit habe ich die linke Seite der Gleichung ziemlich gut bearbeitet.
  Aber, ehm, mit der Rechten komme ich nicht weiter…

  Der Golem schaut dich finster an.

  **Robo**: Du willst `sum_univ_castSucc` auf der rechten Seite anwenden, aber es
  gibt mehrere Orte, wo das Lemma passen würde.
  Deshalb musst du mit `rw [sum_univ_castSucc (n := {n} + 1)]` angeben, wo genau.

  **Du**: Was bedeutet das?

  **Robo** Das Lemma hat eine Annahme `n` und du sagst ihm explizit, was es für dieses `n`
  einsetzen muss, nämlich `{n} + 1`"
  Branch
    rw [Fin.sum_univ_castSucc]
    Hint "**Robo**: Das hat jetzt einfach `Fin.sum_univ_castSucc` am ersten Ort angewendet,
    wo das möglich war. Das ist nicht so ideal, die like Seite war schon okay.

    **Robo**: Geh doch zurück und bring `rw` dazu am anderen Ort umzuschreiben."
  rw [Fin.sum_univ_castSucc (n := n + 1)]
  simp
  Hint "**Robo**: `add_pow_two` ist auch noch nützlich!"
  rw [add_pow_two]
  Hint "**Du**: Ich glaube, ich sehe hier ne arithmetische Summe drin!!

  **Robo**: Ich habe dir das dies von vorhin temporär als `arithmetic_sum` gespeichert,
  damit du diese brauchen kannst."
  rw [arithmetic_sum]
  Hint "**Du**: Jetzt sollten es eigentlich nur noch arithmetische Operationen sein."
  ring

NewLemma arithmetic_sum add_pow_two
LemmaTab "Sum"

Conclusion "Der Golem denkt ganz lange nach, und ihr bekommt das Gefühl, dass er gar nie
aggressiv war, sondern nur eine sehr tiefe Stimme hat.

Mit einem kleinen Erdbeben setzt er sich hin und winkt euch dankend zu.

Damit zieht ihr weiter durch die karge Landschaft auf diesem Planet."
