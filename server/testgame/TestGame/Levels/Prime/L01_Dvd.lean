import TestGame.Metadata

import Mathlib.Tactic.Ring

Game "TestGame"
World "Prime"
Level 1

Title "Teilbarkeit"

Introduction
"
Die Aussage \"$m$ teilt $n$.\" wird in Lean als `m | n` (`\\|`) geschrieben.

**Wichtig:** `∣` (Teilbarkeit) ist ein spezielles Unicode Symbol, das nicht dem
senkrechten Strich auf der Tastatur (`|`) entspricht. Man erhält es mit `\\|`.

`m ∣ n` bedeutet `∃ c, n = m * c`, das heisst, man kann damit genau gleich umgehen
wie mit einem `∃`-Quantifier.
"

Statement dvd_add
  "Wenn $m$ ein Teiler von $n$ und $k$ ist, dann teilt es die Summe."
  (n m k : ℕ) (h : m ∣ n) (g : m ∣ k) : m ∣ n + k := by
  rcases h with ⟨x, h⟩
  rcases g with ⟨y, g⟩
  use x + y
  rw [h, g]
  ring

HiddenHint (n : ℕ) (m : ℕ) (k : ℕ) (h : m ∣ n) (g : m ∣ k) : m ∣ n + k =>
"
Wenn man explizit mit der Definition von Teilbarkeit arbeiten will,
sollte man als erstes alle Annahmen der Form `x ∣ y` mit `rcases` aufteilen.
"

HiddenHint (n : ℕ) (m : ℕ) (k : ℕ) (x : ℕ) (h : n = m * x) (g : m ∣ k) : m ∣ n + k =>
"
Wenn man explizit mit der Definition von Teilbarkeit arbeiten will,
sollte man als erstes alle Annahmen der Form `x ∣ y` mit `rcases` aufteilen.
"

HiddenHint (n : ℕ) (m : ℕ) (k : ℕ) (y : ℕ)  (h : m ∣ n) (g : k = m * y) : m ∣ n + k =>
"
Wenn man explizit mit der Definition von Teilbarkeit arbeiten will,
sollte man als erstes alle Annahmen der Form `x ∣ y` mit `rcases` aufteilen.
"

HiddenHint (n : ℕ) (m : ℕ) (k : ℕ) (x : ℕ) (y : ℕ) (h : n = m * x) (g : k = m * y) : m ∣ n + k =>
"
Jetzt kannst du mit `use` eine Zahl angeben, so dass $m * X = n + k$.
"
