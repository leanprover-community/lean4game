import Lean

-- show all available options
instance : ToString Lean.OptionDecl where
  toString a := toString a.defValue ++ ", [" ++ toString a.group ++ "]: " ++ toString a.descr

def showOptions : IO Unit := do
  let a <- Lean.getOptionDeclsArray
  IO.println f! "{a}"

#eval showOptions
