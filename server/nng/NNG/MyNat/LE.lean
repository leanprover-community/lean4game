import NNG.MyNat.Multiplication

namespace MyNat

def le (a b : ℕ) :=  ∃ (c : ℕ), b = a + c

-- Another choice is to define it recursively: 
-- | le 0 _
-- | le (succ a) (succ b) = le ab 

-- notation
instance : LE MyNat := ⟨MyNat.le⟩

--@[leakage] theorem le_def' : MyNat.le = (≤) := rfl

theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

end MyNat