import TestGame.Metadata

import Mathlib.Data.Real.Basic      -- definiert `ℝ`
import Mathlib.Algebra.Module.Basic -- definiert `module`
import Mathlib.Tactic.LibrarySearch

set_option tactic.hygienic false

Game "TestGame"
World "Module"
Level 1

Title "Module"

Introduction
"
Vektorräume sind in Lean etwas algemeiner definiert, als dies normalerweise in
einer Einführungsvorlesung antrifft: Man definiert ein \"Modul\" (Plural: Moduln)
über einem Ring. Ein Modul über einem Körper wird auch \"Vektorraum\" genannt.
Konkret heisst das:

Sei `R` ein Ring. Ein `R`-Modul ist eine kommutative Gruppe `(V, +)` zusammen mit
einer Abbildung `• : R × V → V` (Skalarmultiplitation genannt), die folgende
Eigenschaften beliebige `(r s : R)` und `(v w : V)`erfüllt:
- `r • (v + w) = r • v + r • w`
- `(r + s) • v = r • v + s • v`
- `(r * s) • v = r • s • v`
- `1 • r = r`
- `0 • v = 0`
- `r • 0 = 0`

Bemerkungen:
1) Über einem `[field R]` sind die letzten beiden Eigenschaften überflüssig, diese kann
   man beweisen, wenn man Cancellation (`a₁ + x = a₂ + x → a₁ = a₂`) hat. In einem generellen
   Ring, muss das aber nicht gegeben sein (siehe Nullteiler).
2) Die nötigen Annahmen um ein Modul in Lean zu erhalten sind tatsächlich noch etwas lockerer,
   so muss `R` nicht ganz ein Ring sein (nur `[semiring R]`) und
   `V` muss nicht ganz eine kommutative Gruppe sein (nur `[add_comm_monoid V]`).


Einen abstrakten Vektorraum definiert man wie folgt:
`variables {R V : Type*} [field R] [add_comm_monoid V] [module R V]`

Wenn man hingegen konkret zeigen will, dass ein existierendes Objekt ein Vektorraum ist,
kann man eine einsprechende Instanz wie folgt definieren:

```
instance Q_module : Module ℚ ℝ :=
{ smul := λa r, ↑a * r
  smul_zero := _
  zero_smul := _
  one_smul := _
  smul_add := _
  add_smul := _
  mul_smul := _ }
```
Man muss also angeben, welche Skalarmultiplikation man gerne hätte
(`smul`. In unserem Fall sagen wir einfach, diese soll Multiplikation in `ℝ` sein.)
und dazu jegliche Beweise, dass die Skalarmultiplikation sich mit der Ringstruktur verträgt.
Im nachfolgenden beweisen wir die Eigenschaften einzeln.
"

Statement
"Zeige, dass $\\mathbb{R}$ ein $\\mathbb{Q}$-Modul ist."
    : Module ℚ ℝ := by
  refine {
    smul := fun a r => ↑a * r
    smul_zero := ?smul_zero
    zero_smul := ?zero_smul
    one_smul := ?one_smul
    smul_add := ?smul_add
    add_smul := ?add_smul
    mul_smul := ?mul_smul }

  · intro b
    change (1 : ℚ) * b = b
    rw [Rat.cast_one, one_mul]
  · intro x y b
    change (x * y : ℚ) * b = x * (y * b)
    rw [Rat.cast_mul, mul_assoc]
  · intro a
    rw [smul_zero]
  · intro a x y
    change a * (x + y) = a * x + a * y
    rw [mul_add]
  · intro r s x
    change (r + s : ℚ) * x = r * x + s * x
    rw [Rat.cast_add, add_mul]
  · intro a
    change (0 : ℚ) * a = 0
    simp
