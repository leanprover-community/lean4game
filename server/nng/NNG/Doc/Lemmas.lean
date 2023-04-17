import GameServer.Commands

LemmaDoc MyNat.add_zero as "add_zero" in "Nat"
"`add_zero (a : ℕ) : a + 0 = a`

This is one of the two axioms defining addition on `ℕ`."

LemmaDoc MyNat.add_succ as "add_succ" in "Nat"
"`add_succ (a d : ℕ) : a + (succ d) = succ (a + d)`

This is the second axiom definiting addition on `ℕ`"

LemmaDoc MyNat.zero_add as "zero_add" in "Nat"
"(missing)"

LemmaDoc MyNat.add_assoc as "add_assoc" in "Nat"
"(missing)"

LemmaDoc MyNat.succ_add as "succ_add" in "Nat"
"(missing)"

LemmaDoc MyNat.add_comm as "add_comm" in "Nat"
"(missing)"

LemmaDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "Nat"
"(missing)"

LemmaDoc not_iff_imp_false as "not_iff_imp_false" in "Prop"
"(missing)"

LemmaDoc MyNat.succ_inj as "succ_inj" in "Nat"
"(missing)"

LemmaDoc MyNat.zero_ne_succ as "zero_ne_succ" in "Nat"
"(missing)"
