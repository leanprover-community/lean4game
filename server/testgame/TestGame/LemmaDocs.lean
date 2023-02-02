import GameServer.Commands

-- Wird im Level "Implication 11" ohne Beweis angenommen.
LemmaDoc not_not as not_not in "Logic"
"
### Aussage

`¬¬A ↔ A`

### Annahmen

`(A : Prop)`
"

-- Wird im Level "Implication 10" ohne Beweis angenommen.
LemmaDoc not_or_of_imp as not_or_of_imp in "Logic"
"
### Aussage

`¬A ∨ B`

### Annahmen

`(A B : Prop)`\\
`(h : A → B)`
"

-- Wird im Level "Implication 12" bewiesen.
LemmaDoc imp_iff_not_or as imp_iff_not_or in "Logic"
"
### Aussage

`(A → B) ↔ ¬A ∨ B`

### Annahmen

`(A B : Prop)`
"

LemmaDoc zero_add as zero_add in "Addition"
"This lemma says `∀ a : ℕ, 0 + a = a`."

LemmaDoc add_zero as add_zero in "Addition"
"This lemma says `∀ a : ℕ, a + 0 = a`."

LemmaDoc add_succ as add_succ in "Addition"
"This lemma says `∀ a b : ℕ, a + succ b = succ (a + b)`."

LemmaSet addition : "Addition lemmas" :=
zero_add add_zero

LemmaDoc not_forall as not_forall in "Logic"
"`∀ (A : Prop), ¬(∀ x, A) ↔ ∃x, (¬A)`."

LemmaDoc not_exists as not_exists in "Logic"
"`∀ (A : Prop), ¬(∃ x, A) ↔ ∀x, (¬A)`."

LemmaDoc Even as Even in "Nat"
"
`even n` ist definiert als `∃ r, a = 2 * r`.
Die Definition kann man mit `unfold even at *` einsetzen.
"

LemmaDoc Odd as Odd in "Nat"
"
`odd n` ist definiert als `∃ r, a = 2 * r + 1`.
Die Definition kann man mit `unfold odd at *` einsetzen.
"

LemmaDoc not_odd as not_odd in "Nat"
"`¬ (odd n) ↔ even n`"

LemmaDoc not_even as not_even in "Nat"
"`¬ (even n) ↔ odd n`"

LemmaDoc even_square as even_square in "Nat"
"`∀ (n : ℕ), even n → even (n ^ 2)`"




LemmaDoc mem_univ as mem_univ in "Set"
"x ∈ @univ α"

LemmaDoc not_mem_empty as not_mem_empty in "Set"
""

LemmaDoc empty_subset as empty_subset in "Set"
""

LemmaDoc Subset.antisymm_iff as Subset.antisymm_iff in "Set"
""







LemmaSet natural : "Natürliche Zahlen" :=
Even Odd not_odd not_even

LemmaSet logic : "Logik" :=
not_not not_forall not_exists
