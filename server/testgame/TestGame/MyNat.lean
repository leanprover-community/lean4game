axiom MyNat : Type

notation "ℕ" => MyNat

--axiom zero : ℕ

axiom succ : ℕ → ℕ

@[instance] axiom MyOfNat (n : Nat) : OfNat ℕ n

@[instance] axiom myAddition : HAdd ℕ ℕ ℕ

@[instance] axiom myMultiplication : HMul ℕ ℕ ℕ

axiom add_zero : ∀ a : ℕ, a + 0 = a

axiom add_succ : ∀ a b : ℕ, a + succ b = succ (a + b)

@[elab_as_elim] axiom myInduction {P : ℕ → Prop} (n : ℕ) (h₀ : P 0) (h : ∀ n, P n → P (succ n)) : P n

