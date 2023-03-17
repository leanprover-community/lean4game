import GameServer.Commands

-- Wird im Level "Implication 11" ohne Beweis angenommen.
LemmaDoc not_not as "not_not" in "Logic"
"
### Aussage

`¬¬A ↔ A`

### Annahmen

`(A : Prop)`
"

-- Wird im Level "Implication 10" ohne Beweis angenommen.
LemmaDoc not_or_of_imp as "not_or_of_imp" in "Logic"
"
### Aussage

`¬A ∨ B`

### Annahmen

`(A B : Prop)`\\
`(h : A → B)`
"

-- Wird im Level "Implication 12" bewiesen.
LemmaDoc imp_iff_not_or as "imp_iff_not_or" in "Logic"
"
### Aussage

`(A → B) ↔ ¬A ∨ B`

### Annahmen

`(A B : Prop)`
"


LemmaDoc Nat.succ_pos as "Nat.succ_pos" in "Nat"
"
"

LemmaDoc Nat.pos_iff_ne_zero as "Nat.pos_iff_ne_zero" in "Nat"
"
"

LemmaDoc zero_add as "zero_add" in "Addition"
"This lemma says `∀ a : ℕ, 0 + a = a`."

LemmaDoc add_zero as "add_zero" in "Addition"
"This lemma says `∀ a : ℕ, a + 0 = a`."

LemmaDoc add_succ as "add_succ" in "Addition"
"This lemma says `∀ a b : ℕ, a + succ b = succ (a + b)`."

LemmaDoc not_forall as "not_forall" in "Logic"
"`∀ (A : Prop), ¬(∀ x, A) ↔ ∃x, (¬A)`."

LemmaDoc not_exists as "not_exists" in "Logic"
"`∀ (A : Prop), ¬(∃ x, A) ↔ ∀x, (¬A)`."

DefinitionDoc Even as "Even"
"
`even n` ist definiert als `∃ r, a = 2 * r`.
Die Definition kann man mit `unfold even at *` einsetzen.
"

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
"

DefinitionDoc LeftInverse as "LeftInverse"
"
"

DefinitionDoc RightInverse as "RightInverse"
"
"

DefinitionDoc StrictMono as "StrictMono"
"
`StrictMono f` ist definiert als

```
∀ a b, a < b → f a < f b
```

"

LemmaDoc even_iff_not_odd as "even_iff_not_odd" in "Nat"
"`Even n ↔ ¬ (Odd n)`"

LemmaDoc odd_iff_not_even as "odd_iff_not_even" in "Nat"
"`Odd n ↔ ¬ (Even n)`"

LemmaDoc even_square as "even_square" in "Nat"
"`∀ (n : ℕ), Even n → Even (n ^ 2)`"




LemmaDoc mem_univ as "mem_univ" in "Set"
"x ∈ @univ α"

LemmaDoc not_mem_empty as "not_mem_empty" in "Set"
""

LemmaDoc empty_subset as "empty_subset" in "Set"
""

LemmaDoc Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"
""



LemmaDoc Nat.prime_def_lt'' as "Nat.prime_def_lt''" in "Nat"
""


LemmaDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "Sum"
""

LemmaDoc Fin.sum_univ_castSucc as "Fin.sum_univ_castSucc" in "Sum"
""

LemmaDoc Nat.succ_eq_add_one as "Nat.succ_eq_add_one" in "Sum"
""

LemmaDoc Nat.zero_eq as "Nat.succ_eq_add_one" in "Sum"
""

LemmaDoc add_comm as "add_comm" in "Nat"
""

LemmaDoc mul_add as "mul_add" in "Nat"
""

LemmaDoc add_mul as "add_mul" in "Nat"
""

LemmaDoc arithmetic_sum as "arithmetic_sum" in "Sum"
""

LemmaDoc add_pow_two as "add_pow_two" in "Nat"
""

LemmaDoc Finset.sum_comm as "Finset.sum_comm" in "Sum"
""

LemmaDoc Function.comp_apply as "Function.comp_apply" in "Function"
""

LemmaDoc not_le as "not_le" in "Logic"
""

LemmaDoc if_pos as "if_pos" in "Logic"
""

LemmaDoc if_neg as "if_neg" in "Logic"
""

LemmaDoc StrictMono.injective as "StrictMono.injective" in "Function"
""

LemmaDoc StrictMono.add as "StrictMono.add" in "Function"
""

LemmaDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"
""

LemmaDoc Exists.choose as "Exists.choose" in "Function"
""

LemmaDoc Exists.choose_spec as "Exists.choose_spec" in "Function"
""
LemmaDoc congrArg as "congrArg" in "Function"
""
LemmaDoc congrFun as "congrFun" in "Function"
""

LemmaDoc Iff.symm as "Iff.symm" in "Logic"
""

DefinitionDoc Symbol.Subset as "⊆" "Test"
