import Glorious.Semantics.Normalize

namespace Glorious.Semantics

structure Binding where
  module : ModuleId
  name : String
  nameSpace : Namespace
  declaration : DeclId
  authority : DeclHeader
  priority : Nat
  exported : Bool
  deriving Repr

def descendant (child ancestor : ModuleId) : Bool :=
  child.packageId == ancestor.packageId && ancestor.path.isPrefixOf child.path

def visible (sourceContext : ModuleId) (header : DeclHeader) : Bool :=
  match header.visibility with
  | .public => true
  | .package => sourceContext.packageId == header.module.packageId
  | .private => descendant sourceContext header.module
  | .parent => descendant sourceContext { header.module with path := header.module.path.dropLast }

def directBinding (nameSpace : Namespace) (header : DeclHeader) : Binding :=
  ⟨header.module, header.name, nameSpace, header.id, header, 3, header.visibility == .public⟩

def directBindings (program : Program) : List Binding :=
  program.dataTypes.flatMap (fun data =>
    directBinding .type data.header :: data.variants.map (fun v => directBinding .value v.header)) ++
  program.aliases.map (fun a => directBinding .type a.header) ++
  program.traits.map (fun t => directBinding .trait t.header) ++
  program.effects.flatMap (fun e => directBinding .effect e.header :: e.operations.map (fun op => directBinding .value op.header)) ++
  program.functions.map (fun f => directBinding .value f.header) ++
  program.constants.map (fun c => directBinding .value c.header)

def selectBinding (sourceContext : ModuleId) (nameSpace : Namespace) (name : String)
    (bindings : List Binding) : Check Binding := do
  let candidates := bindings.filter fun b => b.module == sourceContext && b.nameSpace == nameSpace && b.name == name
  let priority := candidates.foldl (fun highest b => max highest b.priority) 0
  let candidates := candidates.filter (fun b => b.priority == priority)
  let identities := candidates.map (·.declaration) |>.eraseDups
  match identities with
  | [] => reject .unknownName s!"unresolved name {name}"
  | [_] => getRequired candidates.head? .unknownName s!"unresolved name {name}"
  | _ => reject .ambiguous s!"ambiguous name {name}; declaration selection does not use argument types"

def pathModule (program : Program) (sourceContext : ModuleId) (components : List String) : Check (ModuleId × String) := do
  let name ← getRequired components.getLast? .unknownName "empty path"
  let qualifiers := components.dropLast
  let (base, rest) ← match qualifiers with
    | "crate" :: rest => pure (⟨sourceContext.packageId, []⟩, rest)
    | "self" :: rest => pure (sourceContext, rest)
    | "super" :: rest => do
      require (!sourceContext.path.isEmpty) .unknownName "crate root has no parent"
      pure ({ sourceContext with path := sourceContext.path.dropLast }, rest)
    | first :: rest =>
      match program.packages.find? (fun p => p.name == first) with
      | some dependency => do
        let own ← getRequired (program.packages.find? (fun p => p.id == sourceContext.packageId)) .unknownName "unknown package"
        require (own.id == dependency.id || own.dependencies.contains dependency.id) .privacy "package is outside the supplied dependency closure"
        pure (dependency.root, rest)
      | none => pure (sourceContext, qualifiers)
    | [] => pure (sourceContext, [])
  let target := { base with path := base.path ++ rest }
  require (program.modules.any (fun m => m.identity == target)) .unknownName "path does not name a declared module"
  return (target, name)

def resolve (program : Program) (bindings : List Binding) (sourceContext : ModuleId)
    (nameSpace : Namespace) (path : Path) : Check Binding := do
  let (target, name) ← pathModule program sourceContext path.components
  let binding ← selectBinding target nameSpace name bindings
  require (visible sourceContext binding.authority || (binding.exported && target != sourceContext)) .privacy s!"{name} is private"
  return binding

def bindingEquivalent (a b : Binding) : Bool :=
  a.module == b.module && a.name == b.name && a.nameSpace == b.nameSpace &&
  a.declaration == b.declaration && a.priority == b.priority && a.exported == b.exported

def addBindings (current additions : List Binding) : List Binding :=
  additions.foldl (fun result b => if result.any (bindingEquivalent b) then result else result ++ [b]) current

def importBindings (program : Program) (current : List Binding) (item : Import) : Check (List Binding) := do
  let imported ← if item.glob then do
      let synthetic := item.source.components ++ ["_"]
      let (source, _) ← pathModule program item.module synthetic
      pure (current.filter fun b => b.module == source &&
        (visible item.module b.authority || b.exported))
    else do
      let binding ← resolve program current item.module item.nameSpace item.source
      let operations := if item.includeOperations then
        match program.effects.find? (fun e => e.header.id == binding.declaration) with
        | none => []
        | some effect => effect.operations.map (fun op => directBinding .value op.header)
        else []
      pure (binding :: operations)
  let priority := if item.prelude then 0 else if item.glob then 1 else 2
  imported.mapM fun binding => do
    require (!item.public || binding.exported || binding.authority.visibility == .public)
      .privacy "re-export would expose a private declaration" item.span
    return {
      binding with
      module := item.module, priority, exported := item.public,
      name := if item.glob || binding.nameSpace != item.nameSpace then binding.name else item.aliasName.getD binding.name }

/-- Benign cycles converge because the finite binding relation only grows.
    Unresolved imports are retried; final ambiguity remains an error. -/
def resolveImports (program : Program) : Check (List Binding) := do
  let direct := directBindings program
  for binding in direct do
    let duplicates := direct.filter fun other => binding.module == other.module &&
      binding.nameSpace == other.nameSpace && binding.name == other.name
    require (duplicates.length == 1) .duplicate s!"duplicate declaration {binding.name}" binding.authority.span
  let imports := program.modules.flatMap (·.imports)
  let rec iterate : Nat → List Binding → List Import → Check (List Binding)
    | 0, _, _ => reject .resourceLimit "import fixed point exhausted"
    | fuel + 1, current, pending => do
      let (next, unresolved) := pending.foldl (init := (current, [])) fun (bindings, rest) item =>
        match importBindings program bindings item with
        | .ok additions => (addBindings bindings additions, rest)
        | .error _ => (bindings, rest ++ [item])
      if unresolved.isEmpty then
        -- Recompute all imports once more: an earlier apparently unique import
        -- may have acquired a competing re-export in the same fixed point.
        let expanded ← imports.mapM (importBindings program next)
        let final := addBindings next expanded.flatten
        if final.length != next.length then iterate fuel final imports else
          for binding in final do
            let _ ← selectBinding binding.module binding.nameSpace binding.name final
          return final
      else if next.length == current.length then
        let first ← getRequired unresolved.head? .unknownName "unresolved import"
        let _ ← importBindings program current first
        reject .unknownName "unresolved import cycle" first.span
      else iterate fuel next unresolved
  iterate program.limits.solving direct imports

def validatePackages (program : Program) : Check Unit := do
  require (unique (program.packages.map (·.id))) .duplicate "duplicate package identity"
  let normalized := program.packages.map (fun p => p.name.replace "-" "_")
  require (unique normalized) .duplicate "normalized package names collide"
  for package in program.packages do
    require (package.name == package.name.replace "-" "_") .invalidSource "driver must normalize package names before semantic analysis"
    require (program.modules.any (fun m => m.identity == package.root)) .unknownName "missing package root"
    for dependency in package.dependencies do
      require (program.packages.any (fun p => p.id == dependency)) .unknownName "dependency absent from supplied closure"
  require (unique (program.modules.map (·.identity))) .duplicate "duplicate module identity"
  for moduleDecl in program.modules do
    for child in moduleDecl.children do
      require (child.packageId == moduleDecl.identity.packageId &&
        child.path.dropLast == moduleDecl.identity.path) .invalidSource "module child violates logical module layout"
      require (program.modules.any (fun m => m.identity == child)) .unknownName "declared child module is absent"

def validateFixities (program : Program) : Check Unit := do
  for fixity in program.fixities do
    require (fixity.precedence ≤ 255) .invalidSource "operator precedence exceeds 255" fixity.span
    require ((program.function fixity.target).isSome || (program.operation fixity.target).isSome)
      .unknownName "fixity target is not a resolved callable" fixity.span
    let duplicates := program.fixities.filter fun other => other.module == fixity.module &&
      other.spelling == fixity.spelling &&
      (other.associativity == .prefixOp) == (fixity.associativity == .prefixOp)
    require (duplicates.length == 1) .duplicate "duplicate positional operator binding" fixity.span

end Glorious.Semantics
