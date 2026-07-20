import Init.Data.Format.Basic

/--
Define a low-level `Std.Format.prettyM` facade in the caller's module.

The facade must be expanded in the same module that asks Lean for final LCNF:
Lean 4.32 does not serialize generated monomorphic specializations for a later
module's `LCNF.main` invocation. Expanding this small source adapter locally
keeps the compiler-generated `prettyM` worker in the captured dependency
closure without introducing a second format AST. A facade named `f` receives
public implementation types named `fState` and `fM` in the same namespace.
-/
syntax "#fir_wasm_pretty_facade " ident : command

macro_rules
  | `(#fir_wasm_pretty_facade $name:ident) => do
      let state := Lean.mkIdentFrom name (name.getId.appendAfter "State")
      let renderM := Lean.mkIdentFrom name (name.getId.appendAfter "M")
      let monad := Lean.mkIdentFrom name (name.getId.appendAfter "Monad")
      let pretty := Lean.mkIdentFrom name (name.getId.appendAfter "MonadPrettyFormat")
      `(section
        /-- Concrete state threaded through the low-level `Std.Format.prettyM` facade. -/
        structure $state where
          out : String := ""
          column : Nat := 0

        /--
        A local concrete state monad keeps `prettyM` monomorphic without
        retaining the generic cross-module `Id`/`StateT` implementation as
        part of the Wasm runtime surface. The state uses `Nat` as a raw
        `tobject` carrier so final LCNF does not forget that a state recovered
        from a polymorphic product field is heap-backed. Only values created
        from the facade state below inhabit this carrier.
        -/
        abbrev $renderM (α : Type) := Nat → α × Nat

        @[reducible] def $monad : Monad $renderM where
          pure value := fun raw => (value, raw)
          bind action next := fun raw =>
            let (value, raw) := action raw
            next value raw

        @[reducible] unsafe def $pretty : Std.Format.MonadPrettyFormat $renderM where
          pushOutput string := fun raw =>
            let state : $state := unsafeCast raw
            ((), unsafeCast ({
              out := String.Internal.append state.out string
              column := state.column + String.Internal.length string } : $state))
          pushNewline indent := fun raw =>
            let state : $state := unsafeCast raw
            ((), unsafeCast ({
              out := String.Internal.append state.out
                (String.Internal.pushn "\n" ' ' indent)
              column := indent } : $state))
          currColumn := fun raw =>
            let state : $state := unsafeCast raw
            (state.column, raw)
          startTag _ := fun raw => ((), raw)
          endTags _ := fun raw => ((), raw)

        /--
        Low-level JavaScript-facing rendering facade. Its semantic Wasm ABI is

        `Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject) → String(object)`.

        The caller supplies the ordinary Lean runtime representation of
        `Format`; this function deliberately introduces no second format AST
        or marshaling layer.
        -/
        unsafe def $name (format : Std.Format) (width indent column : Nat) : String :=
          let action : $renderM Unit :=
            @Std.Format.prettyM $renderM format width indent $monad $pretty
          let initial : Nat := unsafeCast ({ column } : $state)
          let result : $state := unsafeCast (action initial).2
          result.out
        end)

namespace Fir.Wasm.PrettyFormat

#fir_wasm_pretty_facade prettyRaw

end Fir.Wasm.PrettyFormat
