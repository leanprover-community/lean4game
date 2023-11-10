import Lean

@[export my_length]
def myLength (s : String) : IO Unit := do
  IO.println "hello"
  IO.println Lean.origin
  IO.println s
  return ()
