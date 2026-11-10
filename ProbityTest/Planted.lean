module

public section

/-! Declarations the axiom audit must refuse, for `ProbityTest.Check`. -/

namespace ProbityTest.Planted

/-- An axiom of the project's own. -/
axiom planted : 1 = 2

/-- A theorem that rests on it. -/
theorem usesPlanted : 1 = 2 := planted

/-- A private theorem that rests on it: the audit sees private declarations too. -/
private theorem usesPlantedPrivately : 2 = 1 := planted.symm

/-- A tree whose children are held in an array, with its `Repr` derived: a `partial def`. -/
inductive Bush where
  | node (children : Array Bush)
  deriving Repr

end ProbityTest.Planted
