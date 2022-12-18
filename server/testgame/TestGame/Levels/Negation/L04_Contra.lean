import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Contradiction"
Level 4

Title "Ad absurdum"

Introduction
"
Im weiteren kann man auch Widersprüche erhalten, wenn man Annahmen der Form
`A ≠ A` (`\\ne`) hat, oder Aussagen der Form
`A = B` hat, wo Lean weiss, dass `A` und `B` unterschiedlich sind, wie zum Beispiel `0 = 1` in `ℕ`.

*Bemerkung:* `X ≠ Y` muss man als `¬ (X = Y)` lesen, und auch so behandeln.
"

Statement
    "Angenommen man hat $a = b = c$ und $a \\ne c$ natürliche Zahlen $a, b, c$.
    Zeige, dass man daraus jede beliebige Aussage beweisen kann."
    (A : Prop) (a b c : ℕ) (g₁ : a = b) (g₂ : b = c) (h : a ≠ c) : A := by
  rw [g₁] at h
  contradiction

Message (A : Prop) (a : ℕ) (b : ℕ) (c : ℕ) (g₁ : a = b) (g₂ : b = c) (h : a ≠ c) : A =>
  "Benütze `rw [...] at ...` um zwei Aussagen zu bekommen die genau das Gegenteil
  aussagen."

Hint (A : Prop) (a : ℕ) (b : ℕ) (g₁ : a = b) (h : a ≠ b) : A =>
  "`X ≠ Y` muss man als `¬ (X = Y)` lesen. Deshalb findet `contradiction` hier direkt
  einen Widerspruch."

Tactics contradiction
