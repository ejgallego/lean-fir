import FirTalos.Correctness.Adapter

namespace FirTalos.Correctness

open Fir.Wasm

/-- Adaptation first validates the exact symbolic input; consumers need not
provide a separate successful source-validator equation. -/
theorem adapt_source_valid
    {source : Fir.Wasm.Module} {target : FirTalos.AdaptedModule}
    (adapted : FirTalos.adapt source = .ok target) :
    Fir.Wasm.validateModule source = .ok () := by
  cases checked : Fir.Wasm.validateModule source with
  | error error =>
      simp only [FirTalos.adapt, checked] at adapted
      contradiction
  | ok value =>
      cases value
      rfl

/-- A successfully adapted module passed Talos's own structural validator. -/
theorem adapt_target_valid
    {source : Fir.Wasm.Module} {target : FirTalos.AdaptedModule}
    (adapted : FirTalos.adapt source = .ok target) :
    target.wasmModule.validate = .ok () := by
  cases sourceValid : Fir.Wasm.validateModule source with
  | error error =>
      simp only [FirTalos.adapt, sourceValid] at adapted
      change Except.error (FirTalos.AdapterError.invalidModule error) =
        Except.ok target at adapted
      contradiction
  | ok _ =>
      simp only [FirTalos.adapt, sourceValid] at adapted
      cases functionsResult : source.functions.toList.mapM (FirTalos.function source) with
      | error error =>
          rw [functionsResult] at adapted
          change Except.error error = Except.ok target at adapted
          contradiction
      | ok functions =>
          rw [functionsResult] at adapted
          let targetModule : Wasm.Module := {
            funcs := functions
            imports := source.imports.toList.map FirTalos.importDecl
            exports := source.exports.toList.filterMap fun name =>
              (source.functions.findIdx? (·.name == name)).map fun index =>
                { name := name.toString
                  funcIdx := source.imports.size + index : Wasm.Export }
            memory := source.memory.map fun memory =>
              { pagesMin := memory.pagesMin, pagesMax := memory.pagesMax }
            memoryExports := source.memory.toList.filterMap fun memory =>
              memory.exportName.map fun name => (name, 0)
            globals := FirTalos.globalDecls source }
          cases targetValid : targetModule.validate with
          | error message =>
              change (match targetModule.validate with
                | .ok _ => _
                | .error message => Except.error
                    (FirTalos.AdapterError.targetValidation message)) =
                  Except.ok target at adapted
              rw [targetValid] at adapted
              contradiction
          | ok _ =>
              have targetEq : target.wasmModule = targetModule := by
                change (match targetModule.validate with
                  | .ok _ => Except.ok {
                      wasmModule := targetModule
                      sourceMap := {
                        functionOrigins := source.imports.map
                          (FirTalos.FunctionOrigin.import ·.key) ++
                          source.functions.map
                            (FirTalos.FunctionOrigin.definition ·.name) } }
                  | .error message => Except.error
                      (FirTalos.AdapterError.targetValidation message)) =
                    Except.ok target at adapted
                rw [targetValid] at adapted
                injection adapted with targetEq
                rw [← targetEq]
              rw [targetEq]
              exact targetValid

/-- Talos validation excludes duplicate public string names, even when two
distinct source `Name`s would have the same `toString` representation. -/
theorem valid_exportNames_nodup
    {module : Wasm.Module}
    (valid : module.validate = .ok ()) :
    (module.exports.map (·.name)).Nodup := by
  have interface : module.checkInterface = .ok () := by
    cases checked : module.checkInterface with
    | error error =>
        simp only [Wasm.Module.validate, checked] at valid
        contradiction
    | ok value =>
        cases value
        simp
  unfold Wasm.Module.checkInterface at interface
  simp only [Bind.bind, Except.bind] at interface
  repeat' split at interface
  all_goals try contradiction
  all_goals simp_all only [List.nodup_append]

private theorem findExport_of_mem_nodup
    {exports : List Wasm.Export} {item : Wasm.Export}
    (unique : (exports.map (·.name)).Nodup)
    (member : item ∈ exports) :
    (exports.find? (·.name = item.name)).map (·.funcIdx) =
      some item.funcIdx := by
  induction exports with
  | nil => simp at member
  | cons head rest ih =>
      have headFresh : head.name ∉ rest.map (·.name) :=
        (List.nodup_cons.mp unique).1
      have restUnique : (rest.map (·.name)).Nodup :=
        (List.nodup_cons.mp unique).2
      rcases List.mem_cons.mp member with same | later
      · subst item
        simp
      · have different : head.name ≠ item.name := by
          intro equal
          apply headFresh
          exact List.mem_map.mpr ⟨item, later, equal.symm⟩
        simp [different, ih restUnique later]

/-- An exported symbolic function retains its exact unified numeric slot in
the adapted module. Talos validation rules out `toString` collisions among
public export names; no injectivity assumption on `Name.toString` is used. -/
theorem adapt_findExport_of_sourceExport
    {source : Fir.Wasm.Module} {target : FirTalos.AdaptedModule}
    {name : Lean.Name} {index : Nat}
    (adapted : FirTalos.adapt source = .ok target)
    (exported : name ∈ source.exports)
    (found : source.functions.findIdx? (·.name == name) = some index) :
    target.wasmModule.findExport name.toString =
      some (source.imports.size + index) := by
  obtain ⟨_, _, layout⟩ := adapt_preserves_module_layout adapted
  have unique := valid_exportNames_nodup (adapt_target_valid adapted)
  let item : Wasm.Export := {
    name := name.toString
    funcIdx := source.imports.size + index }
  have member : item ∈ target.wasmModule.exports := by
    rw [layout]
    simp only [item, List.mem_filterMap]
    exact ⟨name, by simpa using exported, by simp [found]⟩
  exact findExport_of_mem_nodup unique member

end FirTalos.Correctness
