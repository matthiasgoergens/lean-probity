module

public import Lean

public section

/-! `#audit_axioms M₁ M₂ …`: every declaration of the imported modules under each `Mᵢ` may rest only on Lean's three
standard axioms.  This refuses `sorryAx` (an unfinished proof), the auxiliary axiom `native_decide` adds for each use,
the compiler axioms `Lean.ofReduceBool` and `Lean.trustCompiler`, any axiom the project declares itself, and a derived
instance compiled as a `partial def` (`derivedPartial`), which rests on no axiom.  It walks the whole environment, so a
new theorem needs no entry anywhere.  Run it from a file that is not a `module`, which loads the private declarations
of the modules it imports too.  The roots of a project's executables cannot all be imported into one file, since each
defines `main`: audit them from one file each. -/

namespace Probity.AxiomAudit

open Lean Elab Command

/-- The axioms a declaration may use. -/
meta def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `name` is a `partial def` a deriving handler wrote: an opaque constant compiled from its
`_unsafe_rec` implementation, as Lean keeps a `partial def`, under an instance (each handler writes its
function under the instance it derives, `instReprValue.repr`).  `deriving Repr`, `BEq`, `Hashable`, `Ord`,
`ToJson` and `FromJson` write one for a nested inductive (one held in an `Array` or `List` of itself).  A
`partial def` written in the source is the principles rule lean:partial-def's, which reads the keyword
and cannot see these. -/
meta def derivedPartial (env : Environment) (name : Name) : Bool :=
  (env.find? name matches some (.opaqueInfo _)) && env.contains (name ++ `_unsafe_rec) &&
    Meta.isInstanceCore env name.getPrefix

/-- `#audit_axioms M₁ M₂ …` checks every declaration of the imported modules under each `Mᵢ`:
an error per declaration that uses an axiom outside `allowedAxioms` or is a `derivedPartial`
(which no axiom shows: a `partial def` rests on none), otherwise one line saying
how many declarations it checked and one `axiom audit module: M` per imported module it audited,
which `check.sh` reads to know which modules the audits covered. -/
elab "#audit_axioms " roots:ident+ : command => do
  let env ← getEnv
  let roots := roots.map (·.getId)
  let modules := env.header.moduleNames
  -- each imported declaration with its module; one whose module has no name would escape the audit
  let mut declared : Array (Name × Name) := #[]
  for (name, _) in env.constants.map₁ do
    let some i := env.getModuleIdxFor? name
      | throwError "axiom audit: imported declaration {name} has no module index"
    let some module := modules[i.toNat]?
      | throwError "axiom audit: {name} has module index {i.toNat}, which names no imported module"
    declared := declared.push (name, module)
  for root in roots do
    unless declared.any fun (_, module) => root.isPrefixOf module do
      throwError "axiom audit: no declarations in modules under {root}"
  let names := declared.filterMap fun (name, module) =>
    if roots.any (·.isPrefixOf module) then some name else none
  let mut refused := 0
  for name in names.qsort Name.lt do
    let extra := (← collectAxioms name).filter (· ∉ allowedAxioms)
    unless extra.isEmpty do
      logError m!"axiom audit: {name} uses {extra.toList}"
      refused := refused + 1
    if derivedPartial env name then
      logError m!"axiom audit: {name} is a derived instance compiled as a partial def; write the instance \
        by well-founded recursion instead (Probity.reprCtor for Repr)"
      refused := refused + 1
  if refused == 0 then
    logInfo m!"axiom audit: {names.size} declarations under {roots.toList} use only {allowedAxioms}"
    for module in modules.qsort Name.lt do
      if roots.any (·.isPrefixOf module) then
        logInfo m!"axiom audit module: {module.toString (escape := false)}"

end Probity.AxiomAudit
