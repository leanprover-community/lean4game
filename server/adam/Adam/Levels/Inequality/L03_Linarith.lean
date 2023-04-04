import Adam.Metadata
import Adam.Options.MathlibPart

Game "Adam"
World "Inequality"
Level 3

Title "Linarith"

Introduction
"
**dritte Person**: Nah wenn wir so spielen:
"

Statement (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  Hint "**Du**: `simp` geht hier nicht, was mir ja auch einläuchtet.

  **Robo**: Ist auch keine Vereinfachung, die du machen willst. Stattdessen,
  `linarith` kann lineare Gleichungen und Ungleichungen lösen. Das ist das Powertool
  in der hinsicht."
  linarith

NewTactic linarith
NewLemma Nat.pos_iff_ne_zero
LemmaTab "Nat"

Conclusion "**Du**: Naja so beeindruckend war das jetzt auch noch nicht."
