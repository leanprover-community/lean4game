import NNG.MyNat.Definition

namespace MyNat

open MyNat

def add : MyNat → MyNat → MyNat
  | a, 0   => a
  | a, MyNat.succ b => MyNat.succ (MyNat.add a b)

instance : Add MyNat where
  add := MyNat.add

/--
This theorem proves that if you add zero to a MyNat you get back the same number.
-/
theorem add_zero (a : MyNat) : a + 0 = a := by rfl

/--
This theorem proves that (a + (d + 1)) = ((a + d) + 1) for a,d in MyNat.
-/
theorem add_succ (a d : MyNat) : a + (succ d) = succ (a + d) := by rfl
