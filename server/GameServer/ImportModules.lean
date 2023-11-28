import Lean.Environment
import Std.Tactic.OpenPrivate
import Lean.Data.Lsp.Communication

open Lean

structure LoadingParams : Type where
  counter : Nat
  deriving ToJson

-- Code adapted from `Lean/Environment.lean`

partial def importModulesCore' (imports : Array Import) : ImportStateM Unit := do
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let (mod, region) ← readModuleData mFile
    importModulesCore' mod.imports
    modify fun s => { s with
      moduleData  := s.moduleData.push mod
      regions     := s.regions.push region
      moduleNames := s.moduleNames.push i.module
    }

open private mkInitialExtensionStates Environment.mk setImportedEntries finalizePersistentExtensions
  ensureExtensionsArraySize from Lean.Environment

private partial def finalizePersistentExtensions' (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    (← IO.getStdout).writeLspNotification { method := "$/game/loading", param := {counter := i : LoadingParams} }
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]!
      let s := extDescr.toEnvExtension.getState env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltinAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState env { s with state := newState }
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltinAttributes) > prevAttrSize then
        -- This branch is executed when `pExtDescrs[i]` is the extension associated with the `init` attribute, and
        -- a user-defined persistent extension is imported.
        -- Thus, we invoke `setImportedEntries` to update the array `importedEntries` with the entries for the new extensions.
        env ← setImportedEntries env mods prevSize
        -- See comment at `updateEnvAttributesRef`
        env ← updateEnvAttributes env
      loop (i + 1) env
    else
      return env

def finalizeImport' (s : ImportState) (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment := do
  let numConsts := s.moduleData.foldl (init := 0) fun numConsts mod =>
    numConsts + mod.constants.size + mod.extraConstNames.size
  let mut const2ModIdx : HashMap Name ModuleIdx := mkHashMap (capacity := numConsts)
  let mut constantMap : HashMap Name ConstantInfo := mkHashMap (capacity := numConsts)
  for h:modIdx in [0:s.moduleData.size] do
    let mod := s.moduleData[modIdx]'h.upper
    for cname in mod.constNames, cinfo in mod.constants do
      match constantMap.insert' cname cinfo with
      | (constantMap', replaced) =>
        constantMap := constantMap'
        if replaced then
          throwAlreadyImported s const2ModIdx modIdx cname
      const2ModIdx := const2ModIdx.insert cname modIdx
    for cname in mod.extraConstNames do
      const2ModIdx := const2ModIdx.insert cname modIdx
  let constants : ConstMap := SMap.fromHashMap constantMap false
  let exts ← mkInitialExtensionStates
  let env : Environment := Environment.mk
    (const2ModIdx    := const2ModIdx)
    (constants       := constants)
    (extraConstNames := {})
    (extensions      := exts)
    (header          := {
      quotInit     := !imports.isEmpty -- We assume `core.lean` initializes quotient module
      trustLevel   := trustLevel
      imports      := imports
      regions      := s.regions
      moduleNames  := s.moduleNames
      moduleData   := s.moduleData
    })

  let env ← setImportedEntries env s.moduleData
  finalizePersistentExtensions' env s.moduleData opts

def importModules' (imports : Array Import) : IO Environment := do
  withImporting do
    let (_, s) ← importModulesCore' imports |>.run
    let env ← finalizeImport' s imports {} 0
    return env
