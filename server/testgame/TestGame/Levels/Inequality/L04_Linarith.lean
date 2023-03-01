import TestGame.Metadata
import Mathlib.Tactic.Linarith

Game "TestGame"
World "Inequality"
Level 4

Title "Linarith"

Introduction
"
Sobald man mit einem Ring arbeitet, der eine lineare Order hat (also z.B. `ℤ` oder `ℚ`),
ist `linarith` stärker und kann Systeme von Gleichungen und Ungleichungen angehen.

`linarith` kann aber nur mit linearen Ungleichungen umgehen, mit Termen der Form `x ^ 2`
kann es nicht umgehen.
"

Statement
"
Angenommen man hat für zwei Ganzzahlen $x, y$ folgende Ungleichungen.
$$
\\begin{aligned} 5 * y &\\le 35 - 2 * x \\\\ 2 * y &\\le x + 3 \\end{aligned}
$$
Zeige, dass $y \\le 5$.
"
    (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith
