import NNG.MyNat.Multiplication

-- this is one of *three* routes to
-- canonically_ordered_comm_semiring

namespace MyNat

def le (a b : MyNat) :=  ∃ (c : MyNat), b = a + c

-- Another choice is to define it recursively:
-- | le 0 _
-- | le (succ a) (succ b) = le ab

-- notation
instance : LE MyNat := ⟨MyNat.le⟩

theorem le_def' : MyNat.le = (.≤.) := rfl

theorem le_iff_exists_add (a b : MyNat) : a ≤ b ↔ ∃ (c : MyNat), b = a + c := Iff.rfl

def lt_myNat (a b : MyNat) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT MyNat := ⟨lt_myNat⟩

theorem lt :  ∀ (a b : MyNat), a < b ↔ a ≤ b ∧ ¬b ≤ a := fun _ _ => Iff.rfl


end MyNat