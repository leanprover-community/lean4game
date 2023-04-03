import GameServer.Commands

-- Wird im Level "Implication 11" ohne Beweis angenommen.
LemmaDoc Classical.not_not as "not_not" in "Logic"
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

* Mathlib Doc"

LemmaDoc add_succ as "add_succ" in "Addition"
"This lemma says `∀ a b : ℕ, a + succ b = succ (a + b)`.

## Eigenschaften

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

LemmaDoc Set.not_mem_empty as "not_mem_empty" in "Set"
"
`Set.not_mem_empty {α : Type _} (x : α) : x ∉ ∅`

Kein Element ist in der leeren Menge.

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Set`
* Mathlib Doc: [#not_mem_empty](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.not_mem_empty)
"

LemmaDoc Set.subset_empty_iff as "subset_empty_iff" in "Set"
"
`Set.subset_empty_iff.{u} {α : Type u} {s : Set α} : s ⊆ ∅ ↔ s = ∅`

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Set`
* Mathlib Doc: [#empty_subset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.subset_empty_iff)
"

LemmaDoc Set.empty_subset as "empty_subset" in "Set"
"
`Set.empty_subset {α : Type u} (s : Set α) : ∅ ⊆ s`

## Eigenschaften

* `simp`-Lemma: Ja
* Namespace: `Set`
* Mathlib Doc: [#empty_subset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.empty_subset)
"

LemmaDoc Set.Subset.antisymm as "Subset.antisymm" in "Set"
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

LemmaDoc Set.Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"
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

LemmaDoc Set.diff_inter as "diff_inter" in "Set"
"
`{α : Type u} {s t u : Set α} : s \\ (t ∩ u) = s \\ t ∪ s \\ u`

## Eigenschaften
* Namespace: `Set`
* Mathlib Doc: [#Set.diff_inter](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.diff_inter)

"

LemmaDoc Set.union_assoc as "union_assoc" in "Set"
"
` {α : Type u} (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c)`

## Eigenschaften
* Namespace: `Set`
* Mathlib Doc: [#Set.union_assoc](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.union_assoc)

"

LemmaDoc Set.union_diff_distrib as "union_diff_distrib" in "Set"
"
`{α : Type u} {s t u : Set α} : (s ∪ t) \\ u = s \\ u ∪ t \\ u`

## Eigenschaften
* Namespace: `Set`
* Mathlib Doc: [#Set.union_diff_distrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.union_diff_distrib)

"

LemmaDoc Set.univ_union as "univ_union" in "Set"
"
` {α : Type u} {s : Set α} : Set.univ ∪ s = Set.univ`

## Eigenschaften
* Namespace: `Set`
* Mathlib Doc: [#Set.univ_union](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.univ_union)

"

LemmaDoc Nat.prime_def_lt'' as "prime_def_lt''" in "Nat"
"
`Nat.prime_def_lt'' {p : ℕ} :
Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p`

Die bekannte Definition einer Primmzahl in `ℕ`: Eine Zahl (`p ≥ 2`) mit genau zwei Teilern.

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Nat`
* Mathlib Doc: [#Nat.prime_def_lt''](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime.html#Nat.prime_def_lt'')
"

LemmaDoc Finset.sum_add_distrib as "sum_add_distrib" in "Sum"
"

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Finset`
* Mathlib Doc: [#Finset.sum_add_distrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Basic.html#Finset.sum_add_distrib)
"

LemmaDoc Fin.sum_univ_castSucc as "sum_univ_castSucc" in "Sum"
"

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Fin`
* Mathlib Doc: [#sum_univ_castSucc](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html#Fin.sum_univ_castSucc)
"

LemmaDoc Nat.succ_eq_add_one as "succ_eq_add_one" in "Sum"
"

## Eigenschaften

* `simp`-Lemma: Nein
* Namespace: `Nat`
* Mathlib Doc: [#succ_eq_add_one](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.succ_eq_add_one)
"

LemmaDoc ne_eq as "ne_eq" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#ne_eq](https://leanprover-community.github.io/mathlib4_docs/Init/SimpLemmas.html#ne_eq)
"

LemmaDoc Set.eq_empty_iff_forall_not_mem as "eq_empty_iff_forall_not_mem" in "Sum"
"

## Eigenschaften

* Mathlib Doc: [#eq_empty_iff_forall_not_mem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.eq_empty_iff_forall_not_mem)
"

LemmaDoc Nat.zero_eq as "zero_eq" in "Nat"
"

## Eigenschaften

* Mathlib Doc: [#zero_eq](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.zero_eq)
"

LemmaDoc add_comm as "add_comm" in "Nat"
"

## Eigenschaften

* Mathlib Doc: [#add_comm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#add_comm)
"

LemmaDoc mul_add as "mul_add" in "Nat"
"

## Eigenschaften

* Mathlib Doc: [#mul_add](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#mul_add)
"

LemmaDoc add_mul as "add_mul" in "Nat"
"

## Eigenschaften

* Mathlib Doc: [#add_mul](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#add_mul)
"

LemmaDoc arithmetic_sum as "arithmetic_sum" in "Sum"
"

## Eigenschaften

* Not a mathlib lemma.
"

LemmaDoc add_pow_two as "add_pow_two" in "Nat"
"

## Eigenschaften

* Mathlib Doc: [#add_pow_two](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Ring.html#add_pow_two)
"

LemmaDoc Finset.sum_comm as "sum_comm" in "Sum"
"

## Eigenschaften

* Mathlib Doc: [#sum_comm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Basic.html#Finset.sum_comm)
"

LemmaDoc Function.comp_apply as "comp_apply" in "Function"
"

## Eigenschaften

* Mathlib Doc: [#comp_apply](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Function.comp_apply)
"

LemmaDoc not_le as "not_le" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#not_le](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Algebra/Order.html#not_le)
"

LemmaDoc if_pos as "if_pos" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#if_pos](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#if_pos)
"

LemmaDoc if_neg as "if_neg" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#if_neg](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#if_neg)
"

LemmaDoc StrictMono.injective as "StrictMono.injective" in "Function"
"

## Eigenschaften

* Mathlib Doc: [#StrictMono.injective](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Monotone/Basic.html#StrictMono.injective)
"

LemmaDoc StrictMono.add as "StrictMono.add" in "Function"
"

## Eigenschaften

* Mathlib Doc: [#StrictMono.add](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Monoid/Lemmas.html#StrictMono.add)
"

LemmaDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"
"

## Eigenschaften

* Mathlib Doc: [#Odd.strictMono_pow](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Parity.html#Odd.strictMono_pow)
"

LemmaDoc Exists.choose as "Exists.choose" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#Exists.choose](https://leanprover-community.github.io/mathlib4_docs/Std/Logic.html#Exists.choose)
"

LemmaDoc Exists.choose_spec as "Exists.choose_spec" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#Exists.choose_spec](https://leanprover-community.github.io/mathlib4_docs/Std/Logic.html#Exists.choose_spec)
"
LemmaDoc congrArg as "congrArg" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#congrArg](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#congrArg)
"
LemmaDoc congrFun as "congrFun" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#congrFun](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#congrFun)
"

LemmaDoc Iff.symm as "Iff.symm" in "Logic"
"

## Eigenschaften

* Mathlib Doc: [#Iff.symm](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Iff.symm)
"

LemmaDoc not_imp_not as "not_imp_not" in "Logic"
"
`theorem not_imp_not {a : Prop} {b : Prop} : ¬a → ¬b ↔ b → a`

## Eigenschaften

* Mathlib Doc: [#not_imp_not](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#not_imp_not)
"

LemmaDoc Set.nonempty_iff_ne_empty as "nonempty_iff_ne_empty" in "Logic"
"
`theorem Set.nonempty_iff_ne_empty {α : Type u} {s : Set α} : Set.Nonempty s ↔ s ≠ ∅`

## Eigenschaften

* Mathlib Doc: [#nonempty_iff_ne_empty](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.nonempty_iff_ne_empty)
"

LemmaDoc Set.subset_univ as "subset_univ" in "Set"
"
`{α : Type u} {s : Set α} : s ⊆ univ`
"

LemmaDoc Set.not_mem_compl_iff as "not_mem_compl_iff" in "Set"
"
` {α : Type u} {s : Set α} {x : α} : ¬x ∈ sᶜ ↔ x ∈ s`
"

LemmaDoc Set.mem_of_subset_of_mem as "mem_of_subset_of_mem" in "Set"
"
`{α : Type u} {s₁ : Set α} {s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) :
a ∈ s₁ → a ∈ s₂`
"

LemmaDoc Set.compl_eq_univ_diff as "compl_eq_univ_diff" in "Set"
"
` {α : Type u} (s : Set α) :
sᶜ = Set.univ \\ s`
"

LemmaDoc Set.compl_union as "compl_union" in "Set"
"
` {α : Type u} (s t : Set α) :
(s ∪ t)ᶜ = sᶜ ∩ tᶜ`
"

LemmaDoc Set.diff_diff as "diff_diff" in "Set"
"
` {α : Type u} {s t u : Set α} :
(s \\ t) \\ u = s \\ (t ∪ u)`
"

LemmaDoc Set.compl_inter as "compl_inter" in "Set"
"
` {α : Type u} (s t : Set α) :
(s ∩ t)ᶜ = sᶜ ∪ tᶜ`
"

LemmaDoc Set.diff_eq_compl_inter as "diff_eq_compl_inter" in "Set"
"
`{α : Type u} {s t : Set α} : s \\ t = tᶜ ∩ s`
"

LemmaDoc Set.inter_comm as "inter_comm" in "Set"
"
`{α : Type u} (a b : Set α) : a ∩ b = b ∩ a`
"

LemmaDoc Set.mem_compl_iff as "mem_compl_iff" in "Set"
"
`{α : Type u} (s : Set α) (x : α) : x ∈ sᶜ ↔ ¬x ∈ s`
"

LemmaDoc Set.subset_def as "subset_def" in "Set"
"
``
"

LemmaDoc Set.ssubset_def as "ssubset_def" in "Set"
"
``
"

LemmaDoc not_imp as "not_imp" in "Logic"
"
`{a : Prop} {b : Prop} : (a → b) ↔ a ∧ ¬b`
"

LemmaDoc Set.mem_diff as "mem_diff" in "Set"
"
``
"

LemmaDoc Set.mem_insert_iff as "mem_insert_iff" in "Logic"
"
``
"

LemmaDoc Set.mem_singleton_iff as "mem_singleton_iff" in "Set"
"
``
"

LemmaDoc Function.bijective_iff_has_inverse as "bijective_iff_has_inverse" in "Function"
"
``
"

LemmaDoc Set.mem_setOf as "mem_setOf" in "Set"
"
``
"

LemmaDoc Set.mem_powerset_iff as "mem_powerset_iff" in "Set"
"
``
"

LemmaDoc Set.subset_union_of_subset_left as "subset_union_of_subset_left" in "Set"
"
``
"

LemmaDoc Set.subset_union_of_subset_right as "subset_union_of_subset_right" in "Set"
"
``
"

LemmaDoc Set.setOf_or as "setOf_or" in "Set"
"
``
"

LemmaDoc Set.setOf_and as "setOf_and" in "Set"
"
``
"
  LemmaDoc Set.mem_inter_iff as "mem_inter_iff" in "Set"
"
``
"
