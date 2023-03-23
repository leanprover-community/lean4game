import Adam.Metadata
import Mathlib.Data.Nat.Prime

import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Adam.ToBePorted

Game "Adam"
World "Prime"
Level 4

Title "Existiert eindeutig"

Introduction
"
Hier lässt sich noch eine neue Notation einführen: `∃!` bedeutet
\"es existiert ein eindeutiges\" und ist definiert als


"

Statement
"Zeige dass die einzige gerade Primzahl $2$ ist."
    : ∃! p, Nat.Prime p ∧ Even p := by
  use 2
  constructor
  simp
  rintro y ⟨hy, hy'⟩
  rw [←Nat.Prime.even_iff hy]
  assumption
