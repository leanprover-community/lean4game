import Adam.Metadata

import Adam.ToBePorted
import Adam.Options.MathlibPart

import Adam.Levels.Sum.L03_ArithSum

Game "Adam"
World "Sum"
Level 4

Title "Summe aller ungeraden Zahlen"

Introduction
"
**Du**: Haben eigentlich alle Türme hier so kryptische Beschreibungen am Eingang?

Du gehst zu einem etwas kleineren Nachbarsturm.
"
set_option tactic.hygienic false

open Fin

open BigOperators

Statement
    "$\\sum_{i = 0}^n (2n + 1) = n ^ 2$."
    (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  Hint "**Robo**: Das funktioniert genau gleich wie zuvor, viel Glück."
  induction n
  simp
  Hint (hidden := true) "Den Induktionschritt mit Summen willst du
  eigentlich immer mit `rw [sum_univ_castSucc]` beginnen."
  rw [sum_univ_castSucc]
  simp
  rw [n_ih]
  --rw [Nat.succ_eq_add_one]
  ring

LemmaTab "Sum"
