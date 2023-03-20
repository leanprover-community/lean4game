import GameServer.Commands

-- Wird im Level "Implication 11" ohne Beweis angenommen.
LemmaDoc not_not as "not_not" in "Logic"
"
`not_not {A : Prop} : ¬¬A ↔ A`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `Classical`
* Minimal Import: `Std.Logic`
* Mathlib Doc: [#not_not](https://leanprover-community.github.io/mathlib4_docs/Std/Logic.html#Classical.not_not)
"

-- Wird im Level "Implication 10" ohne Beweis angenommen.
LemmaDoc not_or_of_imp as "not_or_of_imp" in "Logic"
"
`not_or_of_imp {A B : Prop} : (A → B) → ¬A ∨ B`

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `-`
* Minimal Import: `Mathlib.Logic.Basic`
* Mathlib Doc: [#not_or_of_imp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#not_or_of_imp)
"

-- Wird im Level "Implication 12" bewiesen.
LemmaDoc imp_iff_not_or as "imp_iff_not_or" in "Logic"
"
`imp_iff_not_or {A B : Prop} : (A → B) ↔ (¬A ∨ B)`

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `-`
* Minimal Import: `Mathlib.Logic.Basic`
* Mathlib Doc: [#imp_iff_not_or](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#imp_iff_not_or)
"

LemmaDoc Nat.succ_pos as "succ_pos" in "Nat"
"
`Nat.succ_pos (n : ℕ) : 0 < n.succ`

$n + 1$ ist strikt grösser als Null.

## Eigenschaften

* `simp` Lemma: Nein
* Namespace: `Nat`
* Minimal Import: `Mathlib.Init.Prelude`
* Mathlib Doc: [#Nat.succ_pos](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Nat.succ_pos)
"

LemmaDoc Nat.pos_iff_ne_zero as "pos_iff_ne_zero" in "Nat"
"
`Nat.pos_iff_ne_zero {n : ℕ} : 0 < n ↔ n ≠ 0`

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Nat`
* Minimal Import: `Std.Data.Nat.Lemmas`
* Mathlib Doc: [#Nat.pos_iff_ne_zero](https://leanprover-community.github.io/mathlib4_docs/Std/Data/Nat/Lemmas.html#Nat.pos_iff_ne_zero)
"

-- TODO: Not minimal description
LemmaDoc zero_add as "zero_add" in "Addition"
"
`zero_add (a : ℕ) : 0 + a = a`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `-`
* Import: `Mathlib.Nat.Basic`
* Mathlib Doc: [#zero_add](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#zero_add)
"

LemmaDoc add_zero as "add_zero" in "Addition"
"
This lemma says `∀ a : ℕ, a + 0 = a`.

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc"

LemmaDoc add_succ as "add_succ" in "Addition"
"This lemma says `∀ a b : ℕ, a + succ b = succ (a + b)`.

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()"

LemmaDoc not_forall as "not_forall" in "Logic"
"
`not_forall {α : Sort _} {P : α → Prop} : ¬(∀ x, → P x) ↔ ∃ x, ¬P x`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `-`
* Minimal Import: `Mathlib.Logic.Basic`
* Mathlib Doc: [#not_forall](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#not_forall)
"

LemmaDoc not_exists as "not_exists" in "Logic"
"
`not_exists {α : Sort _} {P : α → Prop} : (¬∃ x, P x) ↔ ∀ (x : α), ¬P x.

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `-`
* Minimal Import: `Std.Logic`
* Mathlib Doc: [#not_exists](https://leanprover-community.github.io/mathlib4_docs/Std/Logic.html#not_exists)"

LemmaDoc Nat.even_iff_not_odd as "even_iff_not_odd" in "Nat"
"
`even_iff_not_odd  {n : ℕ} : Even n ↔ ¬Odd n`

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Nat`
* Minimal Import: `Mathlib.Data.Nat.Parity`
* Mathlib Doc: [#Nat.even_iff_not_odd](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Parity.html#Nat.even_iff_not_odd)"

LemmaDoc Nat.odd_iff_not_even as "odd_iff_not_even" in "Nat"
"
`Nat.odd_iff_not_even {n : ℕ} : Odd n ↔ ¬Even n`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `Nat`
* Minimal Import: `Mathlib.Data.Nat.Parity`
* Mathlib Doc: [#Nat.odd_iff_not_even](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Parity.html#Nat.odd_iff_not_even)"

LemmaDoc even_square as "even_square" in "Nat"
"
`even_square : (n : ℕ), Even n → Even (n ^ 2)`

## Eigenschaften

* `simp`-Lemma: Nein
* *Nicht in Mathlib*
"




LemmaDoc Set.mem_univ as "mem_univ" in "Set"
"
`Set.mem_univ {α : Type _} (x : α) : x ∈ @univ α`

Jedes Element ist in `univ`, der Menge aller Elemente eines Typs `α`.

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `Set`
* Minimal Import: `Mathlib.Data.Set.Basic`
* Mathlib Doc: [#mem_univ](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.mem_univ)
"

LemmaDoc not_mem_empty as "not_mem_empty" in "Set"
"
`Set.not_mem_empty {α : Type _} (x : α) : x ∉ ∅`

Kein Element ist in der leeren Menge.

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Set`
* Minimal Import: `Mathlib.Data.Set.Basic`
* Mathlib Doc: [#not_mem_empty](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.not_mem_empty)
"

LemmaDoc empty_subset as "empty_subset" in "Set"
"
`Set.empty_subset {α : Type u} (s : Set α) : ∅ ⊆ s`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `Set`
* Minimal Import: `Mathlib.Data.Set.Basic`
* Mathlib Doc: [#empty_subset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.empty_subset)
"

LemmaDoc Subset.antisymm as "Subset.antisymm" in "Set"
"
`Set.Subset.antisymm {α : Type u} {a : Set α} {b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b`

Zwei Mengen sind identisch, wenn sowohl $A \\subseteq B$ wie auch $B \\subseteq A$.
## Details

`apply Subset.antisymm` ist eine Möglichkeit Gleichungen von Mengen zu zeigen.
eine andere ist `ext i`, welches Elementweise funktiniert.
Siehe auch
[`#Subset.antisymm_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.Subset.antisymm_iff)
für die Iff-Version.

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Set.Subset`
* Minimal Import: `Mathlib.Data.Set.Basic`
* Mathlib Doc: [#Subset.antisymm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.Subset.antisymm)
"

LemmaDoc Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"
"
`Set.Subset.antisymm_iff {α : Type u} {a : Set α} {b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a`

Zwei Mengen sind identisch, wenn sowohl $A \\subseteq B$ wie auch $B \\subseteq A$.
## Details

`rw [Subset.antisymm_iff]` ist eine Möglichkeit Gleichungen von Mengen zu zeigen.
eine andere ist `ext i`, welches Elementweise funktiniert.
Siehe auch
[`#Subset.antisymm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.Subset.antisymm)
für eine verwandte Version.

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Set.Subset`
* Minimal Import: `Mathlib.Data.Set.Basic`
* Mathlib Doc: [#Subset.antisymm_iff](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.Subset.antisymm_iff)
"


LemmaDoc Nat.prime_def_lt'' as "Nat.prime_def_lt''" in "Nat"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"


LemmaDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Fin.sum_univ_castSucc as "Fin.sum_univ_castSucc" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Nat.succ_eq_add_one as "Nat.succ_eq_add_one" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Nat.zero_eq as "Nat.succ_eq_add_one" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc add_comm as "add_comm" in "Nat"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc mul_add as "mul_add" in "Nat"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc add_mul as "add_mul" in "Nat"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc arithmetic_sum as "arithmetic_sum" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc add_pow_two as "add_pow_two" in "Nat"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Finset.sum_comm as "Finset.sum_comm" in "Sum"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Function.comp_apply as "Function.comp_apply" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc not_le as "not_le" in "Logic"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc if_pos as "if_pos" in "Logic"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc if_neg as "if_neg" in "Logic"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc StrictMono.injective as "StrictMono.injective" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc StrictMono.add as "StrictMono.add" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Exists.choose as "Exists.choose" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Exists.choose_spec as "Exists.choose_spec" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"
LemmaDoc congrArg as "congrArg" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"
LemmaDoc congrFun as "congrFun" in "Function"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

LemmaDoc Iff.symm as "Iff.symm" in "Logic"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"



/-! ## Definitions -/

DefinitionDoc Even as "Even"
"
`even n` ist definiert als `∃ r, a = 2 * r`.
Die Definition kann man mit `unfold even at *` einsetzen.
## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()"

DefinitionDoc Odd as "Odd"
"
`odd n` ist definiert als `∃ r, a = 2 * r + 1`.
Die Definition kann man mit `unfold odd at *` einsetzen.
"

DefinitionDoc Injective as "Injective"
"
`Injective f` ist definiert als

```
∀ a b, f a = f b → a = b
```
definiert.
"

DefinitionDoc Surjective as "Surjective"
"
`Surjective f` ist definiert als

```
∀ a, (∃ b, f a = b)
```
"

DefinitionDoc Bijective as "Bijective"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

DefinitionDoc LeftInverse as "LeftInverse"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

DefinitionDoc RightInverse as "RightInverse"
"

## Eigenschaften

* `simp`-Lemma:
* Namespace: `-`
* Minimal Import: `Mathlib.`
* Mathlib Doc: [#]()
"

DefinitionDoc StrictMono as "StrictMono"
"
`StrictMono f` ist definiert als

```
∀ a b, a < b → f a < f b
```

"


DefinitionDoc Symbol.Subset as "⊆" "Test"
