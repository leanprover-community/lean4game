import NNG.MyNat.Multiplication
namespace MyNat
open MyNat

def pow : ℕ → ℕ → ℕ
| _, zero => one
| m, (succ n) => pow m n * m

instance : Pow ℕ ℕ where
  pow := pow

-- notation a ^ b := pow a b

example : (1 : ℕ) ^ (1 : ℕ) = 1 := rfl

lemma pow_zero (m : ℕ) : m ^ (0 : ℕ) = 1 := rfl

lemma pow_succ (m n : ℕ) : m ^ (succ n) = m ^ n * m := rfl

end MyNat

