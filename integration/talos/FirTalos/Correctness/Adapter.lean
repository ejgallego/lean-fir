import FirTalos.Adapter

namespace FirTalos.Correctness

open Lean

@[simp] theorem importDecl_params (sourceImport : Fir.Wasm.Import) :
    (importDecl sourceImport).params =
      sourceImport.signature.params.toList.map abiKind := rfl

@[simp] theorem importDecl_results (sourceImport : Fir.Wasm.Import) :
    (importDecl sourceImport).results =
      sourceImport.signature.results.toList.map abiKind := rfl

/-- A successfully adapted function retains all physical signature lanes. -/
theorem function_preserves_signature
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {target : Wasm.Function}
    (adapted : function sourceModule source = .ok target) :
    target.params = source.params.toList.map (abiKind ∘ Prod.snd) ∧
      target.locals = source.locals.toList.map (abiKind ∘ Prod.snd) ∧
      target.results = source.results.toList.map abiKind := by
  cases body : instructions sourceModule source [] source.body with
  | error error =>
      simp only [function, body] at adapted
      change Except.error error = Except.ok target at adapted
      contradiction
  | ok targetBody =>
      simp only [function, body] at adapted
      change Except.ok {
        params := source.params.toList.map fun entry => abiKind entry.snd
        locals := source.locals.toList.map fun entry => abiKind entry.snd
        results := source.results.toList.map abiKind
        body := targetBody } = Except.ok target at adapted
      injection adapted with targetEq
      rw [← targetEq]
      simp [Function.comp_def]

/-- A resolved source local becomes the same positional Talos local. -/
theorem instruction_localGet
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {fvarId : FVarId} {index : Nat}
    (found : findFVar? (source.params.toList ++ source.locals.toList) fvarId = some index) :
    instruction sourceModule source [] (.localGet fvarId) = .ok (.localGet index) := by
  rw [instruction, found]
  rfl

/-- A proved object-refined local read retains the same physical Talos local. -/
theorem instruction_localGetObject
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {fvarId : FVarId} {index : Nat}
    (found : findFVar? (source.params.toList ++ source.locals.toList) fvarId = some index) :
    instruction sourceModule source [] (.localGetObject fvarId) = .ok (.localGet index) := by
  rw [instruction, found]
  rfl

/-- A resolved source local assignment becomes the same positional Talos assignment. -/
theorem instruction_localSet
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {fvarId : FVarId} {index : Nat}
    (found : findFVar? (source.params.toList ++ source.locals.toList) fvarId = some index) :
    instruction sourceModule source [] (.localSet fvarId) = .ok (.localSet index) := by
  rw [instruction, found]
  rfl

@[simp] theorem instruction_globalGet
    (sourceModule : Fir.Wasm.Module) (source : Fir.Wasm.Function)
    (labels : List FVarId) (index : Nat) (kind : Fir.Wasm.AbiKind) :
    instruction sourceModule source labels (.globalGet index kind) =
      .ok (.globalGet index) := by rw [instruction]; rfl

@[simp] theorem instruction_globalSet
    (sourceModule : Fir.Wasm.Module) (source : Fir.Wasm.Function)
    (labels : List FVarId) (index : Nat) (kind : Fir.Wasm.AbiKind) :
    instruction sourceModule source labels (.globalSet index kind) =
      .ok (.globalSet index) := by rw [instruction]; rfl

/-- A resolved branch target becomes its de Bruijn label depth. -/
theorem instruction_br
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {labels : List FVarId} {label : FVarId} {index : Nat}
    (found : findLabel? labels label = some index) :
    instruction sourceModule source labels (.br label) = .ok (.br index) := by
  rw [instruction, found]
  rfl

/-- A resolved symbolic call becomes the corresponding Talos function index. -/
theorem instruction_call
    {sourceModule : Fir.Wasm.Module} {source : Fir.Wasm.Function}
    {target : Fir.Wasm.CallTarget} {index : Nat}
    (found : callIndex? sourceModule target = some index) :
    instruction sourceModule source [] (.call target) = .ok (.call index) := by
  rw [instruction, found]
  rfl

/--
Successful whole-module adaptation exposes the exact executable layout used by
the proof bridge: mapped imports, pointwise adapted functions, and positional
exports in the unified function-index space.
-/
theorem adapt_preserves_module_layout
    {source : Fir.Wasm.Module} {target : AdaptedModule}
    (adapted : adapt source = .ok target) :
    ∃ functions,
      source.functions.toList.mapM (function source) = .ok functions ∧
        target.wasmModule = {
          funcs := functions
          imports := source.imports.toList.map importDecl
          memory := source.memory.map fun memory =>
            { pagesMin := memory.pagesMin, pagesMax := memory.pagesMax }
          memoryExports := source.memory.toList.filterMap fun memory =>
            memory.exportName.map fun name => (name, 0)
          globals := globalDecls source
          exports := source.exports.toList.filterMap fun name =>
            (source.functions.findIdx? (·.name == name)).map fun index =>
              { name := name.toString
                funcIdx := source.imports.size + index : Wasm.Export } } := by
  cases sourceValid : Fir.Wasm.validateModule source with
  | error error =>
      simp only [adapt, sourceValid] at adapted
      change Except.error (AdapterError.invalidModule error) = Except.ok target at adapted
      contradiction
  | ok sourceValidation =>
      simp only [adapt, sourceValid] at adapted
      cases functionsResult : source.functions.toList.mapM (function source) with
      | error error =>
          rw [functionsResult] at adapted
          change Except.error error = Except.ok target at adapted
          contradiction
      | ok functions =>
          rw [functionsResult] at adapted
          let exports := source.exports.toList.filterMap fun name =>
            (source.functions.findIdx? (·.name == name)).map fun index =>
              { name := name.toString, funcIdx := source.imports.size + index : Wasm.Export }
          let targetModule : Wasm.Module := {
            funcs := functions
            imports := source.imports.toList.map importDecl
            memory := source.memory.map fun memory =>
              { pagesMin := memory.pagesMin, pagesMax := memory.pagesMax }
            memoryExports := source.memory.toList.filterMap fun memory =>
              memory.exportName.map fun name => (name, 0)
            globals := globalDecls source
            exports }
          cases targetValid : targetModule.validate with
          | error message =>
              change (match targetModule.validate with
                | .ok _ => _
                | .error message => Except.error (AdapterError.targetValidation message)) =
                  Except.ok target at adapted
              rw [targetValid] at adapted
              contradiction
          | ok targetValidation =>
              change (match targetModule.validate with
                | .ok _ => Except.ok {
                    wasmModule := targetModule
                    sourceMap := {
                      functionOrigins :=
                        source.imports.map (FunctionOrigin.import ·.key) ++
                        source.functions.map (FunctionOrigin.definition ·.name) } }
                | .error message => Except.error (AdapterError.targetValidation message)) =
                  Except.ok target at adapted
              rw [targetValid] at adapted
              injection adapted with targetEq
              refine ⟨functions, rfl, ?_⟩
              rw [← targetEq]

/-- Successful whole-module adaptation preserves the positional import count. -/
theorem adapt_preserves_import_count
    {source : Fir.Wasm.Module} {target : AdaptedModule}
    (adapted : adapt source = .ok target) :
    target.wasmModule.imports.length = source.imports.size := by
  rcases adapt_preserves_module_layout adapted with ⟨functions, _, layout⟩
  rw [layout]
  simp

end FirTalos.Correctness
