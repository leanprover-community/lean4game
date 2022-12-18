import GameServer.Commands
-- import TestGame.MyNat

LemmaDoc zero_add as zero_add in "Addition"
"This lemma says `∀ a : ℕ, 0 + a = a`."

LemmaDoc add_zero as add_zero in "Addition"
"This lemma says `∀ a : ℕ, a + 0 = a`."

LemmaDoc add_succ as add_succ in "Addition"
"This lemma says `∀ a b : ℕ, a + succ b = succ (a + b)`."

LemmaSet addition : "Addition lemmas" :=
zero_add add_zero

LemmaDoc not_not as not_not in "Logic"
"`∀ (A : Prop), ¬¬A ↔ A`."

LemmaDoc not_forall as not_forall in "Logic"
"`∀ (A : Prop), ¬(∀ x, A) ↔ ∃x, (¬A)`."

LemmaDoc not_exists as not_exists in "Logic"
"`∀ (A : Prop), ¬(∃ x, A) ↔ ∀x, (¬A)`."

LemmaDoc even as even in "Nat"
"
`even n` ist definiert als `∃ r, a = 2 * r`.
Die Definition kann man mit `unfold even at *` einsetzen.
"

LemmaDoc odd as odd in "Nat"
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


LemmaSet natural : "Natürliche Zahlen" :=
even odd not_odd not_even

LemmaSet logic : "Logik" :=
not_not not_forall not_exists
