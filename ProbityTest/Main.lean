module

public import ProbityTest.Guards
meta import Probity.CompiledGuard

/-! `guards`: runs the compiled guards of the modules imported here, compiled, and fails on any that does not hold. -/

/-- Every compiled guard of the imported modules. -/
#compiled_guards allGuards

public def main : IO UInt32 := do
  match Probity.CompiledGuard.failing allGuards with
  | [] =>
    IO.println s!"PASS compiled guards: {allGuards.size}"
    return 0
  | failing =>
    for f in failing do IO.eprintln s!"FAIL compiled guard {f}"
    return 1
