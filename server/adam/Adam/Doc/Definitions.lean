import GameServer.Commands

/-! ## Definitions -/

DefinitionDoc Even as "Even"
"
`even n` ist definiert als `∃ r, a = 2 * r`.
Die Definition kann man mit `unfold even at *` einsetzen.
## Eigenschaften

* Mathlib Doc: [#Even](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Parity.html#Even)"

DefinitionDoc Odd as "Odd"
"
`odd n` ist definiert als `∃ r, a = 2 * r + 1`.
Die Definition kann man mit `unfold odd at *` einsetzen.

* Mathlib Doc: [Odd](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Parity.html#Odd)"

DefinitionDoc Injective as "Injective"
"
`Injective f` ist definiert als

```
∀ a b, f a = f b → a = b
```
definiert.

* Mathlib Doc: [Injective](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Function.html#Function.Injective)"

DefinitionDoc Surjective as "Surjective"
"
`Surjective f` ist definiert als

```
∀ a, (∃ b, f a = b)
```

* Mathlib Doc: [Surjective](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Function.html#Function.Surjective)"

DefinitionDoc Bijective as "Bijective"
"

## Eigenschaften

* Mathlib Doc: [#Bijective](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Function.html#Function.Bijective)
"

DefinitionDoc LeftInverse as "LeftInverse"
"

## Eigenschaften

* Mathlib Doc: [#LeftInverse](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Function.html#Function.LeftInverse)
"

DefinitionDoc RightInverse as "RightInverse"
"

## Eigenschaften

* Mathlib Doc: [#RightInverse](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Logic.html#RightInverse)
"

DefinitionDoc StrictMono as "StrictMono"
"
`StrictMono f` ist definiert als

```
∀ a b, a < b → f a < f b
```

## Eigenschaften

* Mathlib Doc: [#StrictMono](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Monotone/Basic.html#StrictMono)

"

DefinitionDoc Disjoint as "Disjoint"
"
"


DefinitionDoc Set.preimage as "preimage"
"
"


DefinitionDoc Set.Nonempty as "Nonempty" "

`A.Nonemty` ist als `∃ x, x ∈ A` definiert.
"


DefinitionDoc Symbol.Subset as "⊆" "

Auf Mengen (`Set`) ist `A ⊆ B` als `∀x, x ∈ A → x ∈ B` implementiert.

Im goal kann man direkt `intro x hx` machen, in einer Annahme, kann man mit `rcases`
loslegen.

Alternativ kann man mit `rw[Set.subset_def]` die Definition explizit einsetzen.
"


DefinitionDoc Symbol.function as "fun x => _" "

Anonyme funktionen kann man mit `fun (x : ℤ) => 2 * x` definieren und
wie andere Objekte verwenden.

Note: `=>` wird in mathlib oft auch `↦` (`\\maps`) geschrieben.
"
