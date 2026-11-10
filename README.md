# Probity

Three small tools that keep a Lean 4 project honest, on the toolchain alone (no Mathlib, no Batteries):

- `#audit_axioms M₁ M₂ …` (`Probity.AxiomAudit`) checks every declaration of the imported modules under the roots `Mᵢ`, not a list of theorems: each may rest only on `propext`, `Classical.choice` and `Quot.sound`.  It refuses `sorryAx`, the axioms `native_decide` and the compiler add, any axiom the project declares, and a derived instance compiled as a `partial def` (which `#print axioms` cannot show, because a `partial def` rests on no axiom).  A new theorem needs no entry anywhere.
- `#compiled_guard e` (`Probity.CompiledGuard`) is a `#guard` that a program runs compiled, instead of the elaborator interpreting it.  A `#guard` needs a `meta import` of the code it calls, and Lake then rebuilds the module after any change below that import and runs every guard again.  A compiled guard only has to typecheck where it is written.  `#compiled_guards name` gathers the guards of the imported modules into one array that a program runs, and `#audit_compiled_guards Root` checks that the program with root `Root` gathers every guard, so that none runs nowhere.  `#run_compiled_guards M` runs a module's guards interpreted, for interactive use.
- `Probity.reprCtor` (`Probity.ReprCtor`) writes `Repr` for a nested inductive (one that holds itself in a `List` or `Array`) by hand, total, with the text `deriving Repr` writes: the derived instance of such a type is a `partial def`, which the axiom audit refuses.

```lean
-- in a module of the project
import Probity.CompiledGuard

def triangle (n : Nat) : Nat := (List.range (n + 1)).foldl (· + ·) 0

#compiled_guard triangle 4 == 10
```

```lean
-- in a file that is not a module, so that it sees private declarations too
import Probity.AxiomAudit
import MyProject

#audit_axioms MyProject
```

`ProbityTest/` has a complete example: guards in a module, a program that gathers and runs them (`lake exe guards`), and the audits, with declarations the axiom audit must refuse.

`import Probity` brings in all three.

## Use

In `lakefile.lean`:

```lean
require probity from git "https://github.com/matthiasgoergens/lean-probity" @ "<commit>"
```

or in `lakefile.toml`:

```toml
[[require]]
name = "probity"
git = "https://github.com/matthiasgoergens/lean-probity"
rev = "<commit>"
```

The toolchain is in `lean-toolchain`.  `lake test` checks the examples in `ProbityTest/`.

## Licence

Apache License 2.0; see `LICENSE`.
