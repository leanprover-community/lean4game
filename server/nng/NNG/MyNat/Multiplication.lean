import NNG.MyNat.Addition

namespace MyNat

open MyNat

def mul : MyNat → MyNat → MyNat
  | _, 0   => 0
  | a, b + 1 => a + (MyNat.mul a b)

instance : Mul MyNat where
  mul := MyNat.mul

axiom mul_zero (a : MyNat) : a * 0 = 0

axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a
