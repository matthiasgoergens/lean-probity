module

public import Probity.CompiledGuard
public import Probity.ReprCtor

public section

namespace ProbityTest

/-- A tree whose children are held in a list: a nested inductive, whose derived `Repr` would be a `partial def`. -/
inductive Tree where
  | node (label : Nat) (children : List Tree)

open Probity in
/-- `Tree`'s `Repr`, total: the text `deriving Repr` writes. -/
def Tree.repr : Tree → Nat → Std.Format
  | .node label children, prec =>
    reprCtor ``Tree.node [reprArg label, reprArg (children.attach.map fun ⟨c, _⟩ => ReprShown.mk (Tree.repr c))] prec

instance : Repr Tree := ⟨Tree.repr⟩

/-- The sum of the numbers up to `n`. -/
def triangle (n : Nat) : Nat := (List.range (n + 1)).foldl (· + ·) 0

#compiled_guard triangle 4 == 10
#compiled_guard triangle 0 = 0
#compiled_guard toString (repr (Tree.node 1 [.node 2 [], .node 3 []])) ==
  "ProbityTest.Tree.node 1 [ProbityTest.Tree.node 2 [], ProbityTest.Tree.node 3 []]"

end ProbityTest
