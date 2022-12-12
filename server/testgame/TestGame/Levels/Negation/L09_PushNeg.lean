import TestGame.Metadata
import Mathlib.Tactic.PushNeg
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 9

Title "PushNeg"

Introduction
"
Zum Schluss, immer wenn man irgendwo eine Verneinung `¬∃` oder `¬∀` sieht (`\\not`), kann man
mit `push_neg` das `¬` durch den Quantor hindurchschieben.
"

Statement
    "Es existiert keine natürliche Zahl, die grösser als alle anderen.":
    ¬ ∃ (n : ℕ), ∀ (k : ℕ) , odd (n + k) := by
  push_neg
  intro n
  use 3*n + 6
  rw [not_odd]
  unfold even
  use 2*n + 3
  ring

Message (n : ℕ) : (Exists fun k ↦ ¬odd (n + k)) =>
"An dieser Stelle musst du nun ein `k` angeben, sodass `n + k` gerade ist... Benutz `use ...`
mit der richtigen Zahl."

Conclusion ""

Tactics push_neg intro use rw unfold ring
