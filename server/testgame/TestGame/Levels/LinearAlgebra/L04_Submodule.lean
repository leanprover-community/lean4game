import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice

Game "TestGame"
World "Module"
Level 4

Title "Untervektorräume"

Introduction
"
Sei `K` ein Körper und `V` ein `K`-Modul.

```
variable {K V : Type _} [Field K]
variable [AddCommMonoid V] [Module K V]
```

Untermodule/Untervektorräume werden in Lean ein bisschen anders definiert als Module/Vektorräume.

Grob gesagt ist `V` ein Typ (denke z.B. an eine generelle Menge)
und `[module K V]` eine Instanz, die von Lean automatisc gefunden wird und
sagt, dass auf `V` eine `K`-Modulstruktur existiert. Hingegen ist `submodule K V` die Menge aller
Untermodulen
in `V`. Deshalb definieren wir Untermodule, indem wir Elemente aus dieser Menge auswählen:

```
variable (U : Submodule K V)
```

Unter anderem hat dies den Vorteil, dass `submodule K V` eine Lattice ist, also eine `≤`-Operation
besitzt. Auf dem Papier
schreibt man normalerweise `U₁ ⊆ U₂` um zu sagen, dass das eine Untermodul eine Teilmenge des
anderen ist, in Lean braucht
man dafür immer `≤`.

Ganz `V` als Untermodul von sich selbst betrachtet, schreibt man als `⊤` (`\\top`), also das
grösste Element in dieser Lattice,
und das Null-Untermodule `{0}` with als `⊥` geschrieben (`\\bot`), also das kleinste Element.
"

Statement
"Jeder Untervektorraum `U ⊆ V` ist eine Teilmenge von `V`."
    {K V : Type _} [Field K] [AddCommMonoid V] [Module K V] (U : Submodule K V) : U ≤ ⊤ := by
  simp only [le_top]
