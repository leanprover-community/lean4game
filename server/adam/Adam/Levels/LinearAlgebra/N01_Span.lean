import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Module2"
Level 1

open Submodule

-- Verpackungswahn 1a)
Title "Verpackungswahn"

Introduction
"

"

Statement
""
    {K V : Type _} [Field K] [AddCommMonoid V] [Module K V] (M : Set V) :
    span K ↑(span K M) = span K M := by
  apply Submodule.span_eq
  -- or : simp
