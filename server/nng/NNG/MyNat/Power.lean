import NNG.MyNat.Definition
namespace MyNat
open MyNat

def pow : MyNat → MyNat → MyNat
| _, zero => one
| m, (succ n) => pow m n * m

instance : Pow MyNat MyNat where
  pow := pow

-- notation a ^ b := pow a b

example : (1 : MyNat) ^ (1 : MyNat) = 1 := rfl

lemma pow_zero (m : MyNat) : m ^ (0 : MyNat) = 1 := rfl

lemma pow_succ (m n : MyNat) : m ^ (succ n) = m ^ n * m := rfl

end MyNat

