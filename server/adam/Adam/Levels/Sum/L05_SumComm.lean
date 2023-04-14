import Adam.Metadata

import Adam.ToBePorted
import Adam.Options.MathlibPart

import Adam.Levels.Sum.L04_SumOdd

set_option tactic.hygienic false

open BigOperators
open Finset

Game "Adam"
World "Sum"
Level 5

Title "Summe vertauschen"

Introduction
"
Nun aber zeigt euch eure Begleiterin zwei weitere Türme mit einer kleinen Brücke, die
zwischen den beiden verläuft. Die Tafel am Eingang wurde von einem herunterfallenden Stein
zerstört. Auf der oberen Hälfte steht nur folgendes:

$$\\sum_{i=0}^n\\sum_{j=0}^m a_{ij} = \\sum_{j=0}^m\\sum_{i=0}^n a_{ij}$$

**Du**: Ich glaube, ich kann das in eurem Dialekt formulieren und euch damit helfen!
"


Statement
(n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2^i * (1 + j) : ℕ) =
    ∑ j : Fin m, ∑ i : Fin n, ( 2^i * (1 + j) : ℕ) := by
  Hint "**Robo**: Das sieht gut aus, aber du solltest das kurz beweisen, um sicher zu sein.

  **Du**: Hast du nicht ein Lemma dafür?

  **Robo**: Doch, probier mal `sum_comm`."
  rw [Finset.sum_comm]

NewLemma Finset.sum_comm
LemmaTab "Sum"

Conclusion "
  Euer Begleiter ist ganz begeistert als er dir das Stück Papier aus den Händen nimmt,
  auf dem du die Aussage gekritzelt hast. Gleich zückt sie einen Meißel und beginnt eine
  neue Platte zu erstellen.

  Ihr winkt ihr noch zum Abschied und geht weiter.
"
