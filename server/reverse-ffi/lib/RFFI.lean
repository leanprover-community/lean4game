import Lean

@[export my_length]
def myLength (s : String) : IO Unit := do
  IO.println "hello"
  return () -- IO.println Lean.origin
