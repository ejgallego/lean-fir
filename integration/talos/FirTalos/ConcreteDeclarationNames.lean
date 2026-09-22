import FirTalos.ConcreteReuseCapacityCacheCorrectness

namespace FirTalos.Concrete

open Lean Lean.Compiler Fir.Wasm

private theorem filterMap_filterMapM_of_ok
    {α β γ ε : Type} {f : α → Except ε (Option β)}
    {key : β → Option γ} {selected : α → Option γ}
    {xs : List α} {ys : List β}
    (mapped : xs.filterMapM f = .ok ys)
    (preserved : ∀ x result, f x = .ok result → result.bind key = selected x) :
    ys.filterMap key = xs.filterMap selected := by
  induction xs generalizing ys with
  | nil =>
      simp [List.filterMapM_nil, pure, Except.pure] at mapped
      subst ys
      rfl
  | cons head tail ih =>
      cases headResult : f head with
      | error error =>
          simp [List.filterMapM_cons, headResult, Bind.bind, Except.bind] at mapped
      | ok result =>
          cases tailResult : tail.filterMapM f with
          | error error =>
              cases result <;>
                simp [List.filterMapM_cons, headResult, tailResult,
                  Bind.bind, Except.bind] at mapped
          | ok mappedTail =>
              have headKey := preserved head result headResult
              have tailKeys := ih tailResult
              cases result with
              | none =>
                  simp [List.filterMapM_cons, headResult, tailResult,
                    Bind.bind, Except.bind] at mapped
                  subst ys
                  simpa [List.filterMap_cons, ← headKey] using tailKeys
              | some value =>
                  simp [List.filterMapM_cons, headResult, tailResult,
                    Bind.bind, Except.bind, pure, Except.pure] at mapped
                  subst ys
                  simp [List.filterMap_cons, ← headKey, tailKeys]

private def externalName? (declaration : LCNF.Decl .impure) : Option Name :=
  match declaration.value with
  | .extern _ => some declaration.name
  | .code _ => none

private def internalName? (declaration : LCNF.Decl .impure) : Option Name :=
  match declaration.value with
  | .extern _ => none
  | .code _ => some declaration.name

private theorem declarationNames_partition (declarations : List (LCNF.Decl .impure)) :
    (declarations.map (·.name)).Perm
      (declarations.filterMap externalName? ++ declarations.filterMap internalName?) := by
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      cases valueEq : declaration.value with
      | extern metadata =>
          simpa [externalName?, internalName?, valueEq] using ih.cons declaration.name
      | code code =>
          simpa [externalName?, internalName?, valueEq] using
            List.perm_cons_append_cons declaration.name ih

private theorem externalImport_name
    {declaration : LCNF.Decl .impure} {import_ : Fir.Wasm.Import}
    (imported : Fir.Wasm.externalImport declaration = .ok import_) :
    import_.declaration? = some declaration.name := by
  unfold Fir.Wasm.externalImport at imported
  cases signatureResult :
      Fir.Wasm.ExternalTypes.signature {
        params := declaration.params.map (·.type)
        result := declaration.type } with
  | error error => simp [signatureResult] at imported
  | ok signature =>
      simp only [signatureResult, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at imported
      subst import_
      rfl

/-- Lowering preserves the complete population of declaration names, including
duplicates. Runtime imports contribute no declaration name; external and
internal declarations occupy their respective generated tables. -/
theorem declarationNames_perm_of_lower
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source) :
    (program.decls.toList.map (·.name)).Perm
      (source.imports.toList.filterMap (·.declaration?) ++
        source.functions.toList.map (·.name)) := by
  have functions := LoweredInternalDeclaration.functions_of_lower lowered
  have functionList : program.decls.toList.filterMapM
      (Fir.Wasm.lowerDecl program (Fir.Wasm.cachedDeclarationNames program)) =
      .ok source.functions.toList := by
    rw [← Array.toList_filterMapM, functions]
    rfl
  have functionNames := filterMap_filterMapM_of_ok
      (key := fun function : Fir.Wasm.Function => some function.name)
      (selected := internalName?) functionList (by
    intro declaration result mapped
    cases valueEq : declaration.value with
    | extern metadata =>
        simp [Fir.Wasm.lowerDecl, Fir.Wasm.lowerDeclWithClosureCandidates,
          valueEq, pure, Except.pure] at mapped
        subst result
        simp [internalName?, valueEq]
    | code code =>
        obtain ⟨function, rfl⟩ := lowerDecl_some_of_code valueEq mapped
        obtain ⟨row⟩ := LoweredInternalDeclaration.exists_of_lowerDecl valueEq mapped
        simp [internalName?, valueEq, row.sourceFunctionName])
  obtain ⟨externalImports, importsEq, externalMapped⟩ :=
    LoweredInternalDeclaration.imports_of_lower lowered
  have externalList := congrArg (Functor.map Array.toList) externalMapped
  rw [Array.toList_filterMapM] at externalList
  have externalNames := filterMap_filterMapM_of_ok
      (key := Fir.Wasm.Import.declaration?) (selected := externalName?) externalList (by
    intro declaration result mapped
    cases valueEq : declaration.value with
    | code code =>
        simp [valueEq, pure, Except.pure] at mapped
        subst result
        simp [externalName?, valueEq]
    | extern metadata =>
        cases imported : Fir.Wasm.externalImport declaration with
        | error error => simp [valueEq, imported] at mapped
        | ok import_ =>
            simp [valueEq, imported, pure, Except.pure] at mapped
            subst result
            simpa [externalName?, valueEq] using externalImport_name imported)
  have runtimeNames :
      (((Fir.Wasm.collectRuntimeOps source.functions).mapIdx Fir.Wasm.runtimeImport).toList.filterMap
        Fir.Wasm.Import.declaration?) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro import_ member
    obtain ⟨index, inBounds, rfl⟩ := Array.exists_of_mem_mapIdx (by simpa using member)
    rfl
  simp only [List.filterMap_eq_map'] at functionNames
  rw [importsEq, Array.toList_append, List.filterMap_append, runtimeNames,
    List.nil_append, externalNames, functionNames]
  exact declarationNames_partition program.decls.toList

/-- A generated symbolic module's declaration-name uniqueness reflects back
to the source program; lowering success alone is not a uniqueness check. -/
theorem namesUnique_of_lower_namesNodup
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source)
    (namesNodup : (source.imports.toList.filterMap (·.declaration?) ++
      source.functions.toList.map (·.name)).Nodup) :
    program.NamesUnique := by
  have sourceNames := (declarationNames_perm_of_lower lowered).nodup_iff.mpr namesNodup
  simpa [Fir.LeanIR.Program.NamesUnique, List.nodup_iff_pairwise_ne,
    List.pairwise_map] using sourceNames

end FirTalos.Concrete
