module


public section

namespace Probity

/-! `Repr` for a nested inductive (one whose constructors hold it inside an `Array` or `List`), as
`deriving Repr` writes it but total: the derived instance of a nested inductive is a `partial def`.
A hand-written `reprPrec` builds each constructor with `reprCtor` and gives the children it holds in
a container as `ReprShown` values, so that `Array`, `List` and pairs format them as they format any
element, and the text is the derived instance's. -/

/-- A value's `reprPrec`, ready to apply: what a nested inductive's `reprPrec` maps its children in
a container to. -/
structure ReprShown where
  reprPrec : Nat → Std.Format

instance : Repr ReprShown := ⟨fun s prec => s.reprPrec prec⟩

/-- One constructor's `repr`, as `deriving Repr` writes it (Lean/Elab/Deriving/Repr.lean): its full
name, then its explicit arguments each on a possible line break, in parentheses at `max_prec`. -/
def reprCtor (name : Lean.Name) (args : List Std.Format) (prec : Nat) : Std.Format :=
  Repr.addAppParen (.group (.nest (if prec >= max_prec then 1 else 2)
    (args.foldl (fun shown arg => shown ++ .line ++ arg) (.text (toString name))))) prec

end Probity
