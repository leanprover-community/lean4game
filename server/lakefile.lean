import Lake
open Lake DSL

package nng {
  -- add package configuration options here
}

lean_lib NNG {
  -- add library configuration options here
}

lean_lib NNG.levels {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe nng {
  root := `Main
  supportInterpreter := true
}
