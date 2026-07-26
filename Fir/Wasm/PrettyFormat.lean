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
syntax "#fir_wasm_pretty_trace_facade " ident : command

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

/--
Expand a low-level `Std.Format.prettyM` facade that retains the complete
`MonadPrettyFormat` output/tag protocol.

The returned trace deliberately stores events in reverse chronological order
so recording an event is one list constructor. Consumers reverse the list
while decoding. Keeping the rendered text alongside those events supports
both exact styled comparisons and the existing text projection without
pulling the substantially larger `Lean.Widget.TaggedText` dependency closure
into the compiler artifact.
-/
macro_rules
  | `(#fir_wasm_pretty_trace_facade $name:ident) => do
      let event := Lean.mkIdentFrom name (name.getId.appendAfter "Event")
      let trace := Lean.mkIdentFrom name (name.getId.appendAfter "Trace")
      let state := Lean.mkIdentFrom name (name.getId.appendAfter "State")
      let renderM := Lean.mkIdentFrom name (name.getId.appendAfter "M")
      let monad := Lean.mkIdentFrom name (name.getId.appendAfter "Monad")
      let pretty := Lean.mkIdentFrom name (name.getId.appendAfter "MonadPrettyFormat")
      `(section
        /-- One exact operation observed at the `MonadPrettyFormat` boundary. -/
        structure $event where
          /-- `0`: output, `1`: newline, `2`: start tag, `3`: end tags. -/
          kind : Nat
          /-- Output payload; empty for the three numeric event kinds. -/
          text : String
          /-- Indent, tag, or count payload; zero for output events. -/
          value : Nat
          deriving BEq, Repr

        /--
        Raw styled result. `eventsRev` is the reverse chronological
        `MonadPrettyFormat` event stream.
        -/
        structure $trace where
          text : String
          eventsRev : List $event
          deriving BEq, Repr

        /-- Concrete state threaded through the styled `Std.Format.prettyM` facade. -/
        structure $state where
          out : String := ""
          eventsRev : List $event := []
          column : Nat := 0

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
              eventsRev :=
                ({ kind := 0, text := string, value := 0 } : $event) ::
                  state.eventsRev
              column := state.column + String.Internal.length string } : $state))
          pushNewline indent := fun raw =>
            let state : $state := unsafeCast raw
            ((), unsafeCast ({
              out := String.Internal.append state.out
                (String.Internal.pushn "\n" ' ' indent)
              eventsRev :=
                ({ kind := 1, text := "", value := indent } : $event) ::
                  state.eventsRev
              column := indent } : $state))
          currColumn := fun raw =>
            let state : $state := unsafeCast raw
            (state.column, raw)
          startTag tag := fun raw =>
            let state : $state := unsafeCast raw
            ((), unsafeCast ({
              state with eventsRev :=
                ({ kind := 2, text := "", value := tag } : $event) ::
                  state.eventsRev } : $state))
          endTags count := fun raw =>
            let state : $state := unsafeCast raw
            ((), unsafeCast ({
              state with eventsRev :=
                ({ kind := 3, text := "", value := count } : $event) ::
                  state.eventsRev } : $state))

        /--
        Low-level JavaScript-facing styled rendering facade. Its semantic Wasm
        boundary is

        `Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject) →
          PrettyTrace(object)`.

        The trace records the exact incremental text/newline/tag protocol;
        callers may project `text` only when styling is intentionally ignored.
        -/
        unsafe def $name (format : Std.Format) (width indent column : Nat) : $trace :=
          let action : $renderM Unit :=
            @Std.Format.prettyM $renderM format width indent $monad $pretty
          let initial : Nat := unsafeCast ({ column } : $state)
          let result : $state := unsafeCast (action initial).2
          { text := result.out, eventsRev := result.eventsRev }
        end)

namespace Fir.Wasm.PrettyFormat

#fir_wasm_pretty_facade prettyRaw
#fir_wasm_pretty_trace_facade prettyTraceRaw

end Fir.Wasm.PrettyFormat
