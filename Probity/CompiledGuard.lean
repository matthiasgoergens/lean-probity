module

public meta import Lean.Elab.Command

public section

/-! `#compiled_guard e`, a `#guard` that a program runs compiled, rather than the compiler interpreting it while the
module elaborates; `#compiled_guards name`, which gathers the compiled guards of a program; and
`#audit_compiled_guards`, which checks that a program gathers every one of them.

A `#guard` runs where its module compiles, interpreted, and needs a `meta import` of the code it calls; Lake hashes the
compiled code below a `meta import` into the importer's trace, so the module compiles again after any change below it,
a private body's included, and runs every guard again.  A compiled guard needs no `meta import`: the module only
elaborates it, so that it must type, and a program runs it.  A compiled guard runs only in a program whose root imports
its module and gathers it (`#compiled_guards`). -/


namespace Probity

/-- A compiled guard: the file it is written in, its text, and the check, which holds if it gives true.  The check is
a function, compiled without lifting its body out (`compiler.extract_closed`), so that a program computes it when it
runs the guard, not when it starts.  No line: the module's compiled code, which a module that meta-imports it hashes,
and its private part, which a module that imports it with `import all` hashes, would change with every line moved above a
guard; the text finds it. -/
structure CompiledGuard where
  file : String
  text : String
  check : Unit → Bool

open Lean Elab Command

namespace CompiledGuard

/-- The namespace, under the one a compiled guard is written in and its module's, of its declaration
(`<module>.compiledGuard.guard<n>`). -/
meta def compiledGuardSpace : String := "compiledGuard"

/-- The place `n` of a compiled guard's declaration (`compiledGuard.guard<n>`) among its module's guards in its
namespace; none for any other name. -/
meta def guardPlace? (name : Name) : Option Nat :=
  match name with
  | .str (.str _ space) last =>
    if space == compiledGuardSpace then (last.dropPrefix? "guard").bind (·.toString.toNat?) else none
  | _ => none

/-- Whether `name` is a compiled guard's declaration (`compiledGuard.guard<n>`). -/
meta def isCompiledGuard (name : Name) : Bool := (guardPlace? name).isSome

/-- The namespace, under the one they are written in, of the compiled guards of the module `module`:
`<module>.compiledGuard`, `<module>` the module's name with `_` for `.`. -/
meta def compiledGuardsOf (module : Name) : Name :=
  .mkSimple ((toString module).replace "." "_") ++ .mkSimple compiledGuardSpace

/-- `#compiled_guard e`: the check `e`, a `Bool` or a decidable proposition as `#guard` takes, elaborated here, so
that it must type, but run by a program that gathers it (`#compiled_guards`).  It is the declaration
`<module>.compiledGuard.guard<n>` under the namespace it is written in, a `CompiledGuard`: `<module>` its module's name
with `_` for `.`, so that guards of two modules written in one namespace do not share a name, and `n` its place among
the module's guards in that namespace, one more than the guards declared there before it.  It is public, in a module
without a public section too, so that a program's root can name it.  Neither its name nor its body (its file, its
text, its check), which is not exposed, holds its line, so that an edit that moves a guard within its namespace leaves
the module's interface, its private part and its compiled code as they were, and one that changes a guard leaves its
interface as it was: neither rebuilds a module that imports it.  Adding or deleting a guard, or moving one to another
namespace, adds or deletes a name.  Only in a `module`, since no program's root, a `module`, can import any other
file. -/
elab tk:"#compiled_guard " e:term : command => do
  let env ← getEnv
  let module ← getMainModule
  unless env.header.isModule do
    throwError "#compiled_guard in {module}, which is not a `module`: no program's root can import it, so the guard \
      would run nowhere; write a #guard"
  let space := (← getCurrNamespace) ++ compiledGuardsOf module
  let n := env.constants.map₂.foldl (init := 1) fun n name _ ↦
    if name.getPrefix == space && isCompiledGuard name then n + 1 else n
  let relative := compiledGuardsOf module ++ .mkSimple s!"guard{n}"
  if env.contains ((← getCurrNamespace) ++ relative) then throwError "#compiled_guard: {relative} is declared already"
  let name := mkIdentFrom tk relative (canonical := true)
  let file := (toString module).replace "." "/" ++ ".lean"
  -- a guard a macro writes (`fixture_def`) has no source text of its own: its syntax, printed
  let source := (e.raw.getSubstring? (withLeading := false) (withTrailing := false)).map toString
    |>.getD (toString e.raw.prettyPrint)
  let text := " ".intercalate (((source.split Char.isWhitespace).filter (!·.isEmpty)).toList.map (·.toString))
  elabCommand (← `(set_option compiler.extract_closed false in public def $name : CompiledGuard :=
    { file := $(quote file), text := $(quote text), check := fun _ ↦ $e }))

/-- The declarations of every compiled guard of the imported modules, each with its module's name, by module,
namespace and place (as written, in each namespace); of the module `only` alone if given. -/
meta def compiledGuardsHere (only : Option Name := none) : CommandElabM (Array (Name × Name)) := do
  let env ← getEnv
  let guardType := mkConst ``CompiledGuard
  let mut guards : Array (Name × Name × Nat) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some place := guardPlace? name | continue
    unless info.type == guardType do continue
    let some i := env.getModuleIdxFor? name | throwError "compiled guard {name} has no module"
    let some module := env.header.moduleNames[i.toNat]?
      | throwError "compiled guard {name} has module index {i.toNat}, which names no imported module"
    if only.all (· == module) then guards := guards.push (module, name, place)
  let order : Name × Name × Nat → Name × Name × Nat → Ordering := fun (m, n, k) (m', n', k') ↦
    (compare m.toString m'.toString).then ((compare n.getPrefix.toString n'.getPrefix.toString).then (compare k k'))
  return (guards.qsort fun g g' ↦ order g g' == Ordering.lt).map fun (module, name, _) ↦ (module, name)

/-- `#compiled_guards name`: the declaration `name`, an array of every compiled guard (`#compiled_guard`)
of the imported modules, by module; with the doc
comment written before it, if any.  A program's root writes it, where every module of the program whose declarations
it can name is imported (`#audit_compiled_guards` checks that this holds them all).  None at all is an error. -/
elab doc?:(docComment)? "#compiled_guards " id:ident : command => do
  let guards ← compiledGuardsHere
  if guards.isEmpty then throwError "#compiled_guards: no #compiled_guard of the imported modules"
  let entries := guards.map fun (_, name) ↦ mkCIdent name
  elabCommand (← `($[$doc?:docComment]? def $id : Array CompiledGuard := #[$entries,*]))

/-- The guards of `guards` that fail, each as `file: text`. -/
def failing (guards : Array CompiledGuard) : List String :=
  guards.toList.filterMap fun g ↦ if g.check () then none else some s!"{g.file}: {g.text}"

/-- `#run_compiled_guards Module`: runs every compiled guard of the imported module `Module` here, interpreted, as
`#guard`s would have run them where that module compiles, and prints the ones that fail (`[]` when none does).  None
in that module is an error.  For interactive use, after `lake build Module`, from standard input:

    printf 'import Module\n#run_compiled_guards Module\n' | lake env lean --stdin

A program that gathers them (`#compiled_guards`) runs the same guards compiled. -/
elab "#run_compiled_guards " id:ident : command => do
  let guards ← compiledGuardsHere (some id.getId)
  if guards.isEmpty then throwError "#run_compiled_guards: no #compiled_guard in {id.getId}"
  let entries := guards.map fun (_, name) ↦ mkCIdent name
  elabCommand (← `(#eval $(mkCIdent ``CompiledGuard.failing) #[$entries,*]))

/-- The imported modules whose declarations the `module` `root` sees where it compiles, as Lean's `importModulesCore`
loads them (Lean/Environment.lean): every module `root` imports, and every module that one of those imports publicly,
or imports at all where `import all` reached it from `root`.  A module reached only through a private import is in
the program, but its declarations are not loaded where the root compiles, and cannot be named there.  `root` itself is
not among them: `#compiled_guards` names imported declarations only.  For a file that sees every imported module's
declarations (one that is not a `module`).  It walks the imported modules from the last to the first, so that it
visits each after every module that imports it: Lean lists a module after its imports, which it checks. -/
meta def seenFrom (env : Environment) (root : Name) : CommandElabM NameSet := do
  let data := env.header.moduleNames.toList.zip env.header.moduleData.toList
  unless data.any fun (module, d) ↦ module == root && d.isModule do
    throwError "#audit_compiled_guards: {root} is not an imported `module`"
  let modules := data.map fun (module, d) ↦ (module, d.imports)
  let mut earlier : NameSet := {}
  for (module, imports) in modules do
    for i in imports do
      unless earlier.contains i.module do
        throwError "#audit_compiled_guards: {module} is listed before its import {i.module}"
    earlier := earlier.insert module
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut all : NameSet := ({} : NameSet).insert root
  for (module, imports) in modules.reverse do
    unless seen.contains module do continue
    for i in imports do
      if i.isExported || all.contains module then seen := seen.insert i.module
      if all.contains module && i.importAll then all := all.insert i.module
  return seen.erase root

/-- `#audit_compiled_guards Root`: checks that the program whose root is the imported module `Root` gathers every
compiled guard of the imported modules: that
the declarations of each such guard's module are ones `Root` sees (`seenFrom`), so that its `#compiled_guards` names
them.  A guard of any other module would run nowhere.  For a file that is not a `module` and imports every module that
holds a compiled guard; it prints how many guards the program runs. -/
elab "#audit_compiled_guards " root:ident : command => do
  let env ← getEnv
  unless env.header.moduleNames.contains root.getId do
    throwError "#audit_compiled_guards: {root.getId} is not imported here"
  let seen ← seenFrom env root.getId
  let guards ← compiledGuardsHere
  let unseen := (guards.map (·.1)).toList.eraseDups.filter (!seen.contains ·)
  unless unseen.isEmpty do
    throwError "#audit_compiled_guards: compiled guards that {root.getId} does not gather, in {unseen}: its \
      `#compiled_guards` names those of the modules it imports and of those they import publicly; import each publicly \
      in {root.getId} or below it (a guard of {root.getId} itself is gathered by no program either)"
  let modules := (guards.map (·.1)).toList.eraseDups.length
  logInfo m!"compiled guards of the modules imported here: {guards.size} in {modules} modules, all gathered by \
    {root.getId}"

end CompiledGuard

end Probity
