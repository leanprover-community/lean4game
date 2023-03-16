import TestGame.Metadata

import Mathlib
import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "Lean"
Level 4

Title "Instanz-Argumente"

Introduction
"**Du**: Also nochmals als Zusammenfassung, dann gibt es 3 Arten von Argumenten,
explizite mit `()`, implizite mit `{}` und Instanzen mit `[]`?

**Robo**: Korrekt. Instanzen sind damit auch Implizite Argumente. Der Unterschied
zwischen `{}` und `[]` ist also *wie* Lean diese füllt.

**Du**: Verstehe, bei den ersten sucht es logisch nach einer richtigen Möglichkeit,
beim zweiten geht's durch alle Instanzen, die es kennt.


**Robo**: Funktioniert hier bei mir nicht, aber wenn du ausserhalb eines Beweises
`#synth Ring ℤ` in ein Dokument schreibt, zeigt dir Lean, ob es eine Instanz finden kann.

**Du**: Ich glaube das macht alles Sinn.

**Robo**: Hier, mach nochmals das Gleiche wie vorhin aber mit @-Syntax um das zu
verinnerlichen:
"

open BigOperators

Statement (m : ℕ) :
      ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i := by
  Hint "*Robo*: Schreibe `rw [@Fin.sum_univ_castSucc _ _ (m + 1)]`
  anstatt `rw [Fin.sum_univ_castSucc (n := m + 1)]`!"
  rw [@Fin.sum_univ_castSucc _ _ (m + 1)]
  rfl

OnlyTactic rw rfl

Conclusion "
**Du**: Danke Robo!

Um zwei weitere Ecken und plötzlich steht ihr wieder vor dem Golem, dem ihr schon begegnet seit.
Dieser lädt euch zum Abendmahl ein. Ihr erfährt, dass er ganz gerne liest und er zeigt euch
sein neustes Buch, das er leider nicht lesen kann. Nich tnur ist es der zweite Band einer Serie
(der Erste hat offensichtlich was mit \"Urbildern\" zu tun), sondern ist es auch in einem
Dialekt geschrieben, der anscheinend nur auf einem Nachbarsmond gesprochen wird.

Ihr beschliesst dem herzlichen Golem zu helfen und beiden Monden einen Besuch abzustatten,
sowohl um den Dialekt zu lernen, wie auch in der Bibliothek auf dem anderen Mond nach dem
ersten Band zu suchen.
"
