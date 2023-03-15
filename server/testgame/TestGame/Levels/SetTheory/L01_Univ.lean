import TestGame.Metadata

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false
set_option autoImplicit false

Game "TestGame"
World "SetTheory"
Level 1

Title "Mengen"

Introduction
"
**Mengitte**: Ich würde leider den Inhalt jenes Buches eh nicht verstehen. Aber der beste Weg für
euch, dieses zu entschlüsseln ist, euch ausgiebig mit der Bevölkerung hier zu unterhalten.
Lebt mit ihnen, redet mit ihnen und ihr werdet die Sprache automatisch lernen.

**Mengitte**: Seit aber vorgewarnt, die Leute hier denken ganz viel über Mengen nach,
womit sie immer *homogene Mengen* meinen. Eine Menge natürlicher Zahlen `{1, 4, 6}` ist
verständlich, aber sowas wie eine Menge `{(2 : ℕ), {3, 1}, \"e\", (1 : ℂ)}` gibt es hier
einfach nicht. Punkt.

**Robo**: Als Kontext: Wenn `A` ein beliebiger `Type` ist, dann ist `(U : Set A)` eine Menge
mit Elementen aus `A`

**Mengitte**: Damit ich weiss, dass ihr euch grundsätzlich mit den Leuten austauschen könnt,
erklärt mir doch folgendes:
"

open Set

Statement mem_univ "" {A : Type} (x : A) : x ∈ (univ : Set A) := by
  trivial

Hint (A : Type) (x : A) : x ∈ (univ : Set A) =>
"**Du**: Also `A` ist ein `Type`, `x` ist ein Element in `A`…

**Robo** … und `univ` ist die Menge aller Elemente in `A`.

**Du** ist das nicht einfach `A` selber?

**Robo** Fast, aber das eine ist ein `Type`, das andere eine Menge, also vom Typ `Set A`.

**Du**: Unlogisch.

**Mengites**: Naja, Typen und Mengen sind halt zwei unterschiedliche Sachen und wenn ihr
über Mengen sprechen wollt, müssen alles Mengen sein.

**Du**: Na gut. Und wieso `x ∈ univ` und nicht `x : univ` wie bei Typen?

**Robo**: Jedes Element `(x : A)` hat entweder die Eigenschaft `x ∈ U` oder `x ∉ U` für eine
Menge `(U : Set A)`. (`\\in`, `\\nin`)

**Du**: Also das ist ja dann trivial. Hoffentlich sehen die das hier auch so…
"

Conclusion "**Mengitte**: Ja das stimmt schon. Dann wünsche ich euch viel Erfolg auf eurer Reise!"
