import Probity.AxiomAudit
import Probity.CompiledGuard
import ProbityTest.Main
import ProbityTest.Planted

/-! The tests of the package, checked when this file compiles.  Not a `module`, so that it sees the private
declarations of the modules it imports. -/

-- The guards hold, run here interpreted.
/-- info: [] -/
#guard_msgs in #run_compiled_guards ProbityTest.Guards

-- The guards' module is gathered by the program's root.
/-- info: compiled guards of the modules imported here: 3 in 1 modules, all gathered by ProbityTest.Main -/
#guard_msgs in #audit_compiled_guards ProbityTest.Main

-- The guards and the hand-written total `Repr` rest only on the standard axioms.
#guard_msgs (drop info) in #audit_axioms ProbityTest.Guards ProbityTest.Main

-- A failing guard is reported with its file and text.
#guard Probity.CompiledGuard.failing #[{ file := "F.lean", text := "1 == 2", check := fun _ => 1 == 2 }] == ["F.lean: 1 == 2"]

-- The audit refuses an axiom of the project's own, what rests on it (a private declaration too), and a derived
-- instance compiled as a `partial def`.
/--
error: axiom audit: ProbityTest.Planted.planted uses [ProbityTest.Planted.planted]
---
error: axiom audit: ProbityTest.Planted.usesPlanted uses [ProbityTest.Planted.planted]
---
error: axiom audit: _private.ProbityTest.Planted.0.ProbityTest.Planted.usesPlantedPrivately uses [ProbityTest.Planted.planted]
---
error: axiom audit: ProbityTest.Planted.instReprBush.repr is a derived instance compiled as a partial def; write the instance by well-founded recursion instead (Probity.reprCtor for Repr)
-/
#guard_msgs (error, drop info) in #audit_axioms ProbityTest.Planted
