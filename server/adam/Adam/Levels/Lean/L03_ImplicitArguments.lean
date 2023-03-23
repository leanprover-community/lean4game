import TestGame.Metadata

import Mathlib
import TestGame.ToBePorted

set_option tactic.hygienic false

Game "TestGame"
World "Lean"
Level 3

Title "Implizite Argumente"

Introduction
"
**Du**: Was mich aber mehr beschäftigt, ist, dass Lemmas manchmal viel mehr Argumente
haben als ich hinschreiben muss.

**Robo**: Lean kann manche Argumente aus dem Kontext erschliessen. Hast du zum Beispiel
ein Lemma von vorhin

```
lemma Fin.sum_univ_castSucc {β : Type _} [AddCommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∑ i : Fin (n + 1), f i = ∑ i : Fin n, f (↑Fin.castSucc.toEmbedding i) + f (Fin.last n) := by
  sorry
```

dann reicht es ja Lean `f` zu geben und daraus kann es herausfinden, was die anderen
(`β`, `n`) sein müssen.

**Robo**: Solche *implizite Argumente* markiert man dann mit `{_ : _}` während
*explizite Arumente* mit `(_ : _)` markiert werden.

**Du**: Dann könnte ich also einfach `Fin.sum_univ_castSucc f` schreiben?

**Robo**: Genau!

**Du**: Und was war dann das `(n := m + 1)` vorhin genau?

**Robo**: Damit kann man im Aussnahmefall die impliziten Argumente doch angeben. Hier haben wir
gesagt, es soll für das Argument `n` den Term `m + 1` einsetzen. Hier mach das doch noch einmal
unter weniger Stress:
"

open BigOperators

Statement (m : ℕ) : ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i := by
  Branch
    rw [Fin.sum_univ_castSucc]
    Hint "**Robo**: Siehst du, ohne die Hilfe macht es das Falsche. Deshalb muss man hier
    explizit mit `Fin.sum_univ_castSucc (n := m + 1)` nachhelfen."
    rw [Fin.sum_univ_castSucc]
    Hint "**Robo**: Na klar, in dem Beispiel kannst du einfach weiter umschreiben bis es
    nicht mehr geht, aber das war nicht der Punkt…"
    rw [Fin.sum_univ_castSucc]
    Hint "**Robo**: Na klar, in dem Beispiel kannst du einfach weiter umschreiben bis es
    nicht mehr geht, aber das war nicht der Punkt…"
    rfl
  rw [Fin.sum_univ_castSucc (n := m + 1)]
  rfl

OnlyTactic rw rfl

Conclusion "**Du**: Gibt es auch noch ander Methoden implizite Argumente anzugeben.

**Robo** `@Fin.sum_univ_castSucc` würde *alle* Argumente explizit machen,
aber das ist unparktischer, weil man dann irgendwie
`@Fin.sum_univ_castSucc _ _ (m + 1)` schreiben müsste.

**Du**: Ah und ich sehe der `_` ist überall in Lean ein Platzhalter, der automatisch
gefüllt wird."
