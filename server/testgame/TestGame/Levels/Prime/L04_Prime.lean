import TestGame.Metadata
import Mathlib.Data.Nat.Prime

import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Prime"
Level 4

Title "Primzahlen"

Introduction
"
Um zu sagen, dass eine natürliche Zahl $n$ eine Primzahl ist, braucht man
eine Aussage `Nat.Prime n`, ähnlich wie `Even n`.

Primzahlen sind ein Objekt in Lean, das genug abstrakt definiert ist, dass es sich
aus mathematischer Sicht nicht lohnt mit der Definition zu arbeiten.

Alle wichtigen Lemmas um mit Primzahlen zu arbeiten sind in
[`import Data.Nat.Prime`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime.html)

Insbesondere `Nat.prime_def_lt''` welches die aus der Schule bekannte Definition einer
Primzahl `Prime p ↔ 2 ≤ p ∧ (∀ m, m ∣ p → m = 1 ∨ m = p)` gibt.

Beachte: In Lean gibt es auch noch den Ausdruck `Prime n`, der beschreibt generelle
Primelemente in einem generellen Ring. Wenn man mit natürlichen
Zahlen arbeitet, ist es besser `Nat.Prime` zu verwenden, obwohl man natürlich zeigen kann
dass die beiden äquivalent sind.
"

Statement
"Zeige dass die einzigen Teiler einer Primzahl $1$ und $p$ sind."
    (p : ℕ) (h : Nat.Prime p) : ∀ (x : ℕ), (x ∣ p) → x = 1 ∨ x = p := by
  rw [Nat.prime_def_lt''] at h
  rcases h with ⟨_, h₂⟩
  assumption

NewLemmas Nat.prime_def_lt''
