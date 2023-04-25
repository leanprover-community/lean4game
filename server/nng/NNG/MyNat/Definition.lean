/-- Our copy of the natural numbers called `MyNat`. -/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat
-- deriving BEq, DecidableEq, Inhabited

@[inherit_doc]
notation "ℕ" => MyNat
-- Note: as long as we do not import `Mathlib.Init.Data.Nat.Notation` this is fine.

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

def myNatFromNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => MyNat.succ (myNatFromNat b)

def natFromMyNat (x : MyNat) : Nat :=
  match x with
  | MyNat.zero   => Nat.zero
  | MyNat.succ b => Nat.succ (natFromMyNat b)

instance ofNat {n : Nat} : OfNat MyNat n where
  ofNat := myNatFromNat n

instance : ToString MyNat where
  toString p := toString (natFromMyNat p)

theorem zero_eq_0 : MyNat.zero = 0 := rfl

def one : MyNat := MyNat.succ 0

-- TODO: Why does this not work here??
-- We do not want `simp` to be able to do anything unless we unlock it manually.
attribute [-simp] MyNat.succ.injEq
