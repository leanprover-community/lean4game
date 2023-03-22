import TestGame.Metadata

import Mathlib.Data.Real.Basic      -- definiert `ℝ`
import Mathlib.Algebra.Module.Basic -- definiert `module`
import Mathlib.Tactic.LibrarySearch
import TestGame.StructInstWithHoles

set_option tactic.hygienic false

Game "TestGame"
World "Module"
Level 1

Title "Module"

Introduction
"
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

"

-- Bemerkungen:
-- 1) Über einem `[field R]` sind die letzten beiden Eigenschaften überflüssig, diese kann
--    man beweisen, wenn man Cancellation (`a₁ + x = a₂ + x → a₁ = a₂`) hat. In einem generellen
--    Ring, muss das aber nicht gegeben sein (siehe Nullteiler).
-- 2) Die nötigen Annahmen um ein Modul in Lean zu erhalten sind tatsächlich noch etwas lockerer,
--    so muss `R` nicht ganz ein Ring sein (nur `[Semiring R]`) und
--    `V` muss nicht ganz eine kommutative Gruppe sein (nur `[add_comm_monoid V]`).
-- Einen abstrakten Vektorraum definiert man wie folgt:
-- `variables {R V : Type*} [field R] [add_comm_monoid V] [module R V]`

-- Wenn man hingegen konkret zeigen will, dass ein existierendes Objekt ein Vektorraum ist,
-- kann man eine einsprechende Instanz wie folgt definieren:

-- ```
-- instance Q_module : Module ℚ ℝ :=
-- { smul := λa r, ↑a * r
--   smul_zero := _
--   zero_smul := _
--   one_smul := _
--   smul_add := _
--   add_smul := _
--   mul_smul := _ }
-- ```
-- Man muss also angeben, welche Skalarmultiplikation man gerne hätte
-- (`smul`. In unserem Fall sagen wir einfach, diese soll Multiplikation in `ℝ` sein.)
-- und dazu jegliche Beweise, dass die Skalarmultiplikation sich mit der Ringstruktur verträgt.
-- Im nachfolgenden beweisen wir die Eigenschaften einzeln.

Statement
"Zeige, dass $\\mathbb{R}$ ein $\\mathbb{Q}$-Modul ist."
    : Module ℚ ℝ := by
  Hint "**Robo**: Als erstes willst du die Stuktur `Modul` aufteilen in einzelne Beweise.
  Der Syntax dafür ist:

  ```
  refine \{ ?..! }
  ```
  "
  refine { ?..! }
  · Hint "**Robo**: Hier musst du die Skalarmultiplikation angeben.
    Benutze dafür `exact fun (a : ℚ) (r : ℝ) => ↑a * r`."
    exact fun (a : ℚ) (r : ℝ) => ↑a * r
  · Hint "**Robo**: Jetzt musst du alle eigenschaften eines $\\mathbb\{Q}$-Moduls zeigen,
    das sind also 6 einzelne Goals."
    intro b
    Hint "**Robo**: Mit `change (1 : ℚ) * b = b` kannst du das Goal umschreiben, damit
    dann andere Taktiken besser damit arbeiten können."
    change (1 : ℚ) * b = b
    Hint "**Robo**: Den Teil kannst du mit `simp` beweisen."
    simp
  · intro x y b
    Hint "**Robo**: Benutze `change` um `•` durch `*` zu ersetzen."
    change (x * y : ℚ) * b = x * (y * b)
    Hint "**Robo**: Mit `simp` und `ring` kannst du den Rest beweisen."
    simp
    ring
  · intro a
    simp
  · intro a x y
    change a * (x + y) = a * x + a * y
    ring
  · intro r s x
    change (r + s : ℚ) * x = r * x + s * x
    simp
    ring
  · intro a
    change (0 : ℚ) * a = 0
    simp

NewTactic refine exact change
