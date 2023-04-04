import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Basis"
Level 2

Title "Lineare Unabhängigkeit"

namespace Ex_LinIndep

scoped notation "ℝ²" => Fin 2 → ℝ

Introduction
"
"

Statement
"Zeige, dass `![1, 0], ![1, 1]` linear unabhängig über `ℝ` sind."
    : LinearIndependent ℝ ![(![1, 0] : ℝ²), ![1, 1]] := by
  Hint "`rw [Fintype.linearIndependent_iff]`"
  rw [Fintype.linearIndependent_iff]
  Hint "`intros c h`"
  intros c h
  Hint "BUG: `simp at h` does not work :("
  simp at h -- doesn't work
  sorry

  -- rw [Fintype.linearIndependent_iff]
  -- intros c h
  -- simp at h
  -- intros i
  -- fin_cases i
  -- swap
  -- { exact h.2 }
  -- { have h' := h.1
  --   rw [h.2, add_zero] at h'
  --   exact h'}

end Ex_LinIndep
