import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Basic
import NNG.Tactic.Rfl

/-! # `simp` tactic

Added `withReducible` to prevent `rfl` proving stuff like `n + 0 = n`.
-/

namespace MyNat

open Lean Meta Elab Tactic

-- @[match_pattern] def MyNat.rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or
non-dependent hypotheses. It has many variants:
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.
  If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with
  `f` are used. This provides a convenient way to unfold `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the
  attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas.
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If
  the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis
  `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the
  other hypotheses.
-/
syntax (name := simp) "simp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? (location)? : tactic

/-
  "simp " (config)? (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[builtin_tactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps

end MyNat


