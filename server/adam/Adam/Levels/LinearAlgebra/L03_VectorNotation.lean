import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Module"
Level 3

Title "Konkrete Vektorräume"

Introduction
"
Beachte dass Skalarmultiplikation mit `•` geschrieben wird, und nicht mit `*`!
"

Statement
""
    : 5 • ![ (2 : ℚ), 5 ] + ![ 1, 0 ] = ![11, 25] := by
  funext i
  fin_cases i <;>
  simp <;>
  ring
