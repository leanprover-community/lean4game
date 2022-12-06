import TestGame.Metadata
import Mathlib.Tactic.Ring

Game "TestGame"
World "Nat"
Level 2

Title "Natürliche Zahlen"

Introduction
"
Ring setzt aber nicht selbständig Annahmen ein, diese muss man zuerst manuell mit `rw` verwenden.
"

Statement (x y : ℕ) (h : x = 2 * y + 1) : x ^ 2 = 4 * y ^ 2 + 3 * y + 1 + y := by
  rw [h]
  ring

Conclusion ""

Tactics ring
