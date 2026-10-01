import Grounded.SourceDeclarations

/-! Declaration-driven inclusion over a finite supplied collection of decoded
files. No ambient file lookup is available. Function and import ownership is
assigned by the module tree, never by a file's position in that collection.
Package identities are driver keys; call and import paths share interpretation. -/
namespace Grounded

abbrev SourcePath := List String

inductive ModuleSource where
  | body (functions : List FunctionSyntax) (imports : List FunctionImportSyntax)
      (children : List (Identifier × Visibility × Option ModuleSource))

def ModuleSource.functions : ModuleSource → List FunctionSyntax
  | .body functions _ _ => functions

def ModuleSource.imports : ModuleSource → List FunctionImportSyntax
  | .body _ imports _ => imports

def ModuleSource.children : ModuleSource → List (Identifier × Visibility × Option ModuleSource)
  | .body _ _ children => children

abbrev SourceFiles := List (SourcePath × ModuleSource)

structure LoadedModule where
  home : Module
  origin : SourcePath
  directory : SourcePath
  source : ModuleSource

def Module.child (home : Module) (name : Identifier) : Module :=
  ⟨home.package, home.path ++ [name]⟩

/-- Module bindings carry their declaring parent's visibility. A public
function inside a hidden module does not itself expose that module path. -/
inductive ModuleReachable (modules : List LoadedModule) (caller : Module) : Module → Prop where
  | root {package} (included : (⟨package, []⟩ : Module) ∈ modules.map LoadedModule.home) :
      ModuleReachable modules caller ⟨package, []⟩
  | child {parent name visibility body}
      (included : parent ∈ modules)
      (ancestor : ModuleReachable modules caller parent.home)
      (declared : (name, visibility, body) ∈ parent.source.children)
      (allowed : visibility.Allows parent.home caller) :
      ModuleReachable modules caller (parent.home.child name)


def childDirectory (directory : SourcePath) (name : Identifier) : SourcePath :=
  directory ++ [name.text]

def childFile (directory : SourcePath) (name : Identifier) : SourcePath :=
  childDirectory directory name ++ [name.text ++ ".glorious"]

mutual
inductive ModuleSource.Loads (files : SourceFiles) :
    Module → SourcePath → SourcePath → ModuleSource → List LoadedModule → Prop where
  | body {home origin directory functions imports children descendants}
      (distinct : (children.map Prod.fst).Nodup)
      (included : ModuleChildrenLoad files home origin directory children descendants) :
      ModuleSource.Loads files home origin directory (.body functions imports children)
        (⟨home, origin, directory, .body functions imports children⟩ :: descendants)

inductive ModuleChildrenLoad (files : SourceFiles) : Module → SourcePath → SourcePath →
    List (Identifier × Visibility × Option ModuleSource) → List LoadedModule → Prop where
  | nil {home origin directory} : ModuleChildrenLoad files home origin directory [] []
  | inline {home origin directory name visibility body rest first tail}
      (included : ModuleSource.Loads files (home.child name) origin
        (childDirectory directory name) body first)
      (remaining : ModuleChildrenLoad files home origin directory rest tail) :
      ModuleChildrenLoad files home origin directory ((name, visibility, some body) :: rest) (first ++ tail)
  | external {home origin directory name visibility body rest first tail}
      (supplied : (childFile directory name, body) ∈ files)
      (included : ModuleSource.Loads files (home.child name) (childFile directory name)
        (childDirectory directory name) body first)
      (remaining : ModuleChildrenLoad files home origin directory rest tail) :
      ModuleChildrenLoad files home origin directory ((name, visibility, none) :: rest) (first ++ tail)
end

structure PackageDependency where
  manifestName : String
  target : Nat

/-- Manifest hyphens normalize before the shared identifier decoder. -/
def PackageDependency.name (dependency : PackageDependency) : Option Identifier :=
  Identifier.decode (dependency.manifestName.map fun character => if character = '-' then '_' else character)

theorem PackageDependency.name_selected (dependency : PackageDependency) (name : Identifier) :
    dependency.name = some name ↔
      name.text = dependency.manifestName.map (fun character => if character = '-' then '_' else character) :=
  Identifier.decode_selected _ name


structure PackageSource where
  identity : Nat
  root : SourcePath
  files : SourceFiles
  dependencies : List PackageDependency

private theorem unique_key_member {α β : Type} {entries : List α} {key : α → β}
    (distinct : (entries.map key).Nodup) {first second : α}
    (left : first ∈ entries) (right : second ∈ entries) (same : key first = key second) : first = second := by
  induction entries with
  | nil => simp at left
  | cons entry rest ih =>
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp left with equal | leftTail
    · subst entry
      rcases List.mem_cons.mp right with equal | rightTail
      · exact equal.symm
      · exact False.elim (absent (same ▸ List.mem_map.mpr ⟨second, rightTail, rfl⟩))
    · rcases List.mem_cons.mp right with equal | rightTail
      · subst entry
        exact False.elim (absent (same ▸ List.mem_map.mpr ⟨first, leftTail, rfl⟩))
      · exact ih distinct leftTail rightTail


def PackageSource.DependenciesValid (package : PackageSource) (packages : List PackageSource) : Prop :=
  (package.dependencies.map PackageDependency.name).Nodup ∧
  ∀ dependency ∈ package.dependencies,
    (∃ name, dependency.name = some name) ∧ dependency.target ∈ packages.map PackageSource.identity

def PackageSource.resolveDependency (package : PackageSource) (name : Identifier) : Option Nat :=
  (package.dependencies.find? fun dependency => decide (dependency.name = some name)).map PackageDependency.target

theorem PackageSource.resolveDependency_selected {package : PackageSource} {name : Identifier} {target : Nat}
    (selected : package.resolveDependency name = some target) :
    ∃ dependency ∈ package.dependencies, dependency.name = some name ∧ dependency.target = target := by
  obtain ⟨dependency, found, same⟩ := Option.map_eq_some_iff.mp selected
  have decoded : dependency.name = some name := by simpa using (List.find?_some found)
  exact ⟨dependency, List.mem_of_find?_eq_some found, decoded, same⟩

theorem PackageSource.DependenciesValid.names_unique {package : PackageSource} {packages : List PackageSource}
    (valid : package.DependenciesValid packages) {first second : PackageDependency}
    (left : first ∈ package.dependencies) (right : second ∈ package.dependencies)
    (same : first.name = second.name) : first = second :=
  unique_key_member valid.1 left right same

theorem PackageSource.DependenciesValid.resolve_existing {package : PackageSource} {packages : List PackageSource}
    (valid : package.DependenciesValid packages) {dependency : PackageDependency}
    (member : dependency ∈ package.dependencies) {name : Identifier} (normalized : dependency.name = some name) :
    package.resolveDependency name = some dependency.target := by
  unfold PackageSource.resolveDependency
  cases found : package.dependencies.find? (fun dependency => decide (dependency.name = some name)) with
  | none =>
    have denied := List.find?_eq_none.mp found dependency member
    exact False.elim (denied (by simp [normalized]))
  | some selected =>
    have decoded : selected.name = some name := by simpa using (List.find?_some found)
    have same := valid.names_unique member (List.mem_of_find?_eq_some found) (normalized.trans decoded.symm)
    cases same
    rfl


/-- Only the caller's declared dependencies grant cross-package namespace
access. Merely supplying a package, or importing one of its dependents, does not. -/
def PackageAccess (packages : List PackageSource) (caller target : Nat) : Prop :=
  ∃ package ∈ packages, package.identity = caller ∧
    (target = caller ∨ ∃ name, package.resolveDependency name = some target)


/-- Select the caller's manifest before interpreting a dependency spelling. -/
def resolvePackageDependency : List PackageSource → Nat → Identifier → Option Nat
  | [], _, _ => none
  | package :: rest, caller, name =>
      if package.identity = caller then package.resolveDependency name
      else resolvePackageDependency rest caller name

def sourceNamespace (packages : List PackageSource) (caller : Module) (name : FunctionName) : Option Module :=
  name.namespace (resolvePackageDependency packages caller.package) caller

theorem resolvePackageDependency.selected {packages : List PackageSource} {caller : Nat}
    {name : Identifier} {target : Nat} (selected : resolvePackageDependency packages caller name = some target) :
    ∃ package ∈ packages, package.identity = caller ∧ package.resolveDependency name = some target := by
  induction packages with
  | nil => cases selected
  | cons package rest ih =>
    simp only [resolvePackageDependency] at selected
    split at selected
    · rename_i owner
      exact ⟨package, by simp, owner, selected⟩
    · obtain ⟨original, member, owner, found⟩ := ih selected
      exact ⟨original, by simp [member], owner, found⟩


theorem resolvePackageDependency.existing {packages : List PackageSource}
    (distinct : (packages.map PackageSource.identity).Nodup) {package : PackageSource}
    (member : package ∈ packages) (name : Identifier) :
    resolvePackageDependency packages package.identity name = package.resolveDependency name := by
  induction packages with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [resolvePackageDependency]
    · have different : head.identity ≠ package.identity := by
        intro same
        exact (List.nodup_cons.mp distinct).1 (List.mem_map.mpr ⟨package, member, same.symm⟩)
      simp only [resolvePackageDependency, if_neg different]
      exact ih (List.nodup_cons.mp distinct).2 member

theorem resolvePackageDependency.reorder (packages : List PackageSource) (reorder : PackageSource → SourceFiles) :
    resolvePackageDependency (packages.map fun package => { package with files := reorder package }) =
      resolvePackageDependency packages := by
  induction packages with
  | nil => rfl
  | cons package rest ih =>
    funext caller name
    by_cases same : package.identity = caller <;>
      simp [resolvePackageDependency, same, ih, PackageSource.resolveDependency]


theorem PackageAccess.reorder (packages : List PackageSource) (reorder : PackageSource → SourceFiles)
    (caller target : Nat) :
    PackageAccess (packages.map fun package => { package with files := reorder package }) caller target ↔
      PackageAccess packages caller target := by
  constructor
  · rintro ⟨package, included, owner, allowed⟩
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp included
    exact ⟨original, member, owner, allowed⟩
  · rintro ⟨package, included, owner, allowed⟩
    exact ⟨{ package with files := reorder package }, List.mem_map.mpr ⟨package, included, rfl⟩,
      owner, allowed⟩


def PackageSource.Loads (package : PackageSource) (modules : List LoadedModule) : Prop :=
  (package.files.map Prod.fst).Nodup ∧ ∃ source,
    (package.root, source) ∈ package.files ∧
    source.Loads package.files ⟨package.identity, []⟩ package.root package.root.dropLast modules

inductive PackagesLoad : List PackageSource → List LoadedModule → Prop where
  | nil : PackagesLoad [] []
  | cons {package packages first rest}
      (head : package.Loads first) (tail : PackagesLoad packages rest) :
      PackagesLoad (package :: packages) (first ++ rest)

/-- Owners come from inclusion, while targets are still source paths. -/
def LoadedModule.importSources (loaded : LoadedModule) : List (Module × FunctionImportSyntax) :=
  loaded.source.imports.map fun source => (loaded.home, source)

def elaborateModuleImports (packages : List PackageSource) (modules : List LoadedModule) : Option (List (List ImportEntry)) :=
  resolveFunctionImports (fun home => resolvePackageDependency packages home.package)
    (modules.flatMap LoadedModule.importSources)


structure SourceClosure (packages : List PackageSource) where
  modules : List LoadedModule
  included : PackagesLoad packages modules
  importBatches : List (List ImportEntry)
  importsResolved : elaborateModuleImports packages modules = some importBatches

/-- These are projections of the one elaborated product, not independent analyses. -/
def SourceClosure.importEntries {packages : List PackageSource} (closure : SourceClosure packages) : List ImportEntry :=
  closure.importBatches.flatMap id

def SourceClosure.imports {packages : List PackageSource} (closure : SourceClosure packages) : List FunctionImport :=
  closure.importEntries.flatMap ImportEntry.bindings

theorem SourceClosure.import_binding_member {packages : List PackageSource} (closure : SourceClosure packages)
    {edge : FunctionImport} (member : edge ∈ closure.imports) : .binding edge ∈ closure.importEntries := by
  obtain ⟨entry, included, selected⟩ := List.mem_flatMap.mp member
  cases entry with
  | «namespace» home target => cases selected
  | binding original =>
    have same := List.mem_singleton.mp selected
    cases same
    exact included


/-- Construct the complete import product, or reject an unresolved path.
This is source elaboration, not execution or a promise of future progress. -/
def SourceClosure.fromModules {packages : List PackageSource} (modules : List LoadedModule)
    (included : PackagesLoad packages modules) : Option (SourceClosure packages) :=
  match resolved : elaborateModuleImports packages modules with
  | none => none
  | some imports => some ⟨modules, included, imports, resolved⟩


theorem SourceClosure.fromModules_complete {packages : List PackageSource} (closure : SourceClosure packages) :
    SourceClosure.fromModules closure.modules closure.included = some closure := by
  cases closure with
  | mk modules included imports resolved =>
    unfold SourceClosure.fromModules
    split
    · rename_i missing
      rw [resolved] at missing
      contradiction
    · rename_i other found
      have same := Option.some.inj (found.symm.trans resolved)
      cases same
      rfl

/-- Source closure does not silently omit an import whose path cannot resolve. -/
theorem SourceClosure.import_source {packages : List PackageSource} (closure : SourceClosure packages)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.source.imports) :
    ∃ entries ∈ closure.importBatches, ∃ target,
      source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target ∧
      entries = source.selection.emit loaded.home target source.visibility := by
  have member : (loaded.home, source) ∈ closure.modules.flatMap LoadedModule.importSources :=
    List.mem_flatMap.mpr ⟨loaded, included, List.mem_map.mpr ⟨source, declared, rfl⟩⟩
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have selected : (closure.modules.flatMap LoadedModule.importSources)[index]? = some (loaded.home, source) := by
    exact List.getElem?_eq_some_iff.mpr ⟨bound, same⟩
  obtain ⟨edge, found, resolved⟩ := resolveFunctionImports.source closure.importsResolved selected
  exact ⟨edge, List.mem_of_getElem? found, FunctionImportSyntax.resolve_selected resolved⟩

/-- Every binding originates in the source group's rules, with unchanged owner
and visibility. Namespace-only group entries never become candidate bindings. -/
theorem SourceClosure.import_origin {packages : List PackageSource} (closure : SourceClosure packages)
    {edge : FunctionImport} (member : edge ∈ closure.imports) :
    ∃ loaded ∈ closure.modules, ∃ source ∈ loaded.source.imports,
      edge.home = loaded.home ∧ edge.visibility = source.visibility ∧
      ∃ target, source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target ∧
        ImportSelection.Emits loaded.home source.visibility target source.selection (.binding edge) := by
  obtain ⟨batch, batchMember, inBatch⟩ := List.mem_flatMap.mp (closure.import_binding_member member)
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp batchMember
  have selected : closure.importBatches[index]? = some batch := by simp [bound, same]
  obtain ⟨owned, found, resolved⟩ := resolveFunctionImports.origin closure.importsResolved selected
  obtain ⟨loaded, included, sourceMember⟩ := List.mem_flatMap.mp (List.mem_of_getElem? found)
  obtain ⟨source, declared, rfl⟩ := List.mem_map.mp sourceMember
  obtain ⟨target, path, batchEq⟩ := FunctionImportSyntax.resolve_selected resolved
  rw [batchEq] at inBatch
  have emitted := source.selection.emit_sound loaded.home target source.visibility (.binding edge) inBatch
  exact ⟨loaded, included, source, declared, emitted.home, emitted.visibility, target, path, emitted⟩

/-- Every source rule contributes its entry to the actual product, including
namespace entries for empty groups and intermediate descent prefixes. -/
theorem SourceClosure.import_emitted {packages : List PackageSource} (closure : SourceClosure packages)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.source.imports)
    {target : Module} (path : source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target)
    {entry : ImportEntry} (emitted : ImportSelection.Emits loaded.home source.visibility target source.selection entry) :
    entry ∈ closure.importEntries := by
  obtain ⟨batch, member, actual, found, batchEq⟩ := closure.import_source included declared
  have same := Option.some.inj (found.symm.trans path)
  cases same
  refine List.mem_flatMap.mpr ⟨batch, member, ?_⟩
  rw [batchEq]
  exact emitted.complete



theorem SourceClosure.fromModules_selected {packages : List PackageSource} {modules : List LoadedModule}
    {included : PackagesLoad packages modules} {closure : SourceClosure packages}
    (built : SourceClosure.fromModules modules included = some closure) : closure.modules = modules := by
  unfold SourceClosure.fromModules at built
  split at built
  · contradiction
  · have same := Option.some.inj built
    cases same
    rfl

/-- Exact construction criterion for import elaboration: every supplied import
path must resolve, including unused explicit imports and empty globs. It requires
only interpretation of finite source paths, not a successful name lookup or run. -/
theorem SourceClosure.fromModules_exists_iff {packages : List PackageSource} (modules : List LoadedModule)
    (included : PackagesLoad packages modules) :
    (∃ closure, SourceClosure.fromModules modules included = some closure) ↔
      ∀ loaded ∈ modules, ∀ source ∈ loaded.source.imports,
        ∃ target, source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target := by
  constructor
  · rintro ⟨closure, built⟩ loaded member source declared
    have modulesEq := SourceClosure.fromModules_selected built
    obtain ⟨_, _, target, path, _⟩ := closure.import_source (modulesEq.symm ▸ member) declared
    exact ⟨target, path⟩
  · intro paths
    have possible : ∀ owned ∈ modules.flatMap LoadedModule.importSources,
        ∃ edge, owned.2.resolve (resolvePackageDependency packages owned.1.package) owned.1 = some edge := by
      intro owned member
      obtain ⟨loaded, loadedIn, sourceMember⟩ := List.mem_flatMap.mp member
      obtain ⟨source, declared, rfl⟩ := List.mem_map.mp sourceMember
      obtain ⟨target, path⟩ := paths loaded loadedIn source declared
      exact ⟨source.selection.emit loaded.home target source.visibility, by simp [FunctionImportSyntax.resolve, path]⟩
    obtain ⟨imports, resolved⟩ := resolveFunctionImports.exists
      (dependencies := fun home => resolvePackageDependency packages home.package) possible
    let closure : SourceClosure packages := ⟨modules, included, imports, resolved⟩
    exact ⟨closure, closure.fromModules_complete⟩


def SourceClosure.homes {packages : List PackageSource} (closure : SourceClosure packages) : List Module :=
  closure.modules.map LoadedModule.home

def LoadedModule.functions (loaded : LoadedModule) : List NamedFunction :=
  loaded.source.functions.map fun source => ⟨source, loaded.home⟩

def SourceClosure.functions {packages : List PackageSource} (closure : SourceClosure packages) : List NamedFunction :=
  closure.modules.flatMap LoadedModule.functions

/-- Package authorization guards the existing unique-identity resolver.
Import traversal and function-body elaboration retain their shared producers. -/
noncomputable def SourceClosure.bindingNames {packages : List PackageSource}
    (closure : SourceClosure packages) (caller home : Module) (name : Identifier) : Option Nat := by
  classical
  exact if PackageAccess packages caller.package home.package
    then if ModuleReachable closure.modules caller home
      then Grounded.functionNames closure.functions closure.imports caller home name else none
    else none

theorem SourceClosure.bindingNames_selected {packages : List PackageSource} (closure : SourceClosure packages)
    {caller home : Module} {name : Identifier} {identity : Nat} :
    closure.bindingNames caller home name = some identity ↔
      PackageAccess packages caller.package home.package ∧
      ModuleReachable closure.modules caller home ∧
        FunctionResolution closure.functions closure.imports caller home name identity := by
  classical
  simp only [SourceClosure.bindingNames]
  split
  · split <;> simp_all [Grounded.functionNames.selected_iff]
  · simp_all


noncomputable def SourceClosure.functionNames {packages : List PackageSource}
    (closure : SourceClosure packages) : Module → FunctionName → Option Nat :=
  resolveFunctionNames (sourceNamespace packages) closure.bindingNames

theorem SourceClosure.functionNames_selected {packages : List PackageSource} (closure : SourceClosure packages)
    {caller : Module} {name : FunctionName} {identity : Nat} :
    closure.functionNames caller name = some identity ↔
      ∃ home, sourceNamespace packages caller name = some home ∧
        PackageAccess packages caller.package home.package ∧
        ModuleReachable closure.modules caller home ∧
        FunctionResolution closure.functions closure.imports caller home name.spelling identity := by
  simp [SourceClosure.functionNames, resolveFunctionNames, Option.bind_eq_some_iff,
    SourceClosure.bindingNames_selected]


/-- Static module inclusion feeds the same elaboration and machine contract.
There is no independently supplied module list or declaration-owner table. -/
def SourceClosure.Admitted {packages : List PackageSource} (closure : SourceClosure packages)
    (program : Program) : Prop :=
  (packages.map PackageSource.identity).Nodup ∧
  (∀ package ∈ packages, package.DependenciesValid packages) ∧
  (∀ entry ∈ closure.importEntries, PackageAccess packages entry.home.package entry.target.package ∧
    ModuleReachable closure.modules entry.home entry.target) ∧
  FunctionImportsValid closure.homes closure.functions closure.imports ∧
  NamedProgramAdmitted closure.functionNames closure.functions program

theorem SourceClosure.Admitted.checked {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) : program.Checked :=
  admitted.2.2.2.2.checked

/-- Import-path authorization comes from actual source admission over the
complete elaborated import product, not an independently supplied namespace. -/
theorem SourceClosure.Admitted.source_import_access {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.source.imports) :
    ∃ target, source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target ∧
      PackageAccess packages loaded.home.package target.package ∧ ModuleReachable closure.modules loaded.home target := by
  obtain ⟨batch, member, target, path, batchEq⟩ := closure.import_source included declared
  obtain ⟨entry, present, owner, targetEq⟩ := source.selection.emit_root loaded.home target source.visibility
  have entryMember : entry ∈ closure.importEntries := List.mem_flatMap.mpr ⟨batch, member, batchEq.symm ▸ present⟩
  obtain ⟨access, reachable⟩ := admitted.2.2.1 entry entryMember
  rw [owner, targetEq] at access reachable
  exact ⟨target, path, access, reachable⟩

/-- All namespace obligations in a grouped source import must hold, not only
those whose leaves are later selected by a call. -/
theorem SourceClosure.Admitted.source_import_entry_access {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.source.imports)
    {target : Module} (path : source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target)
    {entry : ImportEntry} (emitted : ImportSelection.Emits loaded.home source.visibility target source.selection entry) :
    PackageAccess packages entry.home.package entry.target.package ∧ ModuleReachable closure.modules entry.home entry.target :=
  admitted.2.2.1 entry (closure.import_emitted included declared path emitted)



theorem SourceClosure.function_owner {packages : List PackageSource} (closure : SourceClosure packages)
    {declaration : NamedFunction} (member : declaration ∈ closure.functions) :
    ∃ loaded ∈ closure.modules, ∃ source ∈ loaded.source.functions,
      declaration = ⟨source, loaded.home⟩ := by
  obtain ⟨loaded, included, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨source, found, same⟩ := List.mem_map.mp selected
  exact ⟨loaded, included, source, found, same.symm⟩

/-- Supplied-file order does not enter inclusion. This transports the actual
loaded module product, not just an independent name lookup. -/
theorem ModuleSource.Loads.files_congr {first second : SourceFiles}
    (same : ∀ entry, entry ∈ first ↔ entry ∈ second)
    {home : Module} {origin directory : SourcePath} {source : ModuleSource} {modules : List LoadedModule}
    (loaded : source.Loads first home origin directory modules) :
    source.Loads second home origin directory modules := by
  induction loaded using ModuleSource.Loads.rec
    (motive_2 := fun home origin directory children modules _ =>
      ModuleChildrenLoad second home origin directory children modules) with
  | body distinct _ ih => exact .body distinct ih
  | nil => exact .nil
  | inline _ _ head tail => exact .inline head tail
  | external supplied _ _ head tail => exact .external ((same _).mp supplied) head tail

/-- Every selected runtime function has a declaration in an included module.
The owner is produced by inclusion, not supplied as source-function syntax. -/
theorem SourceClosure.Admitted.declaration {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl} (selected : program.functions identity = some declaration) :
    ∃ loaded ∈ closure.modules, ∃ source ∈ loaded.source.functions,
      declaration.home = loaded.home ∧
      NamedFunction.Elaborates program closure.functionNames
        ⟨source, loaded.home⟩ declaration := by
  obtain ⟨_, core, elaborated, functions⟩ := admitted.2.2.2.2
  rw [functions] at selected
  obtain ⟨source, found, body⟩ := elaborated.selected_core selected
  obtain ⟨loaded, included, item, member, same⟩ := closure.function_owner (List.mem_of_getElem? found)
  subst source
  refine ⟨loaded, included, item, member, ?_, body⟩
  cases body
  rfl

/-- General preservation, progress and consumption framing for elaboration
against the declaration-driven closure. No execution-success premise occurs. -/
theorem SourceClosure.Admitted.soundness {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program closure.functionNames
      home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment : Environment} (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    {state : Configuration} (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup :=
  elaborated.soundness slots admitted.checked store issued run


private theorem supplied_file_unique {files : SourceFiles}
    (distinct : (files.map Prod.fst).Nodup) {path : SourcePath} {first second : ModuleSource}
    (left : (path, first) ∈ files) (right : (path, second) ∈ files) : first = second := by
  exact congrArg Prod.snd (unique_key_member distinct left right rfl)

theorem ModuleSource.Loads.deterministic {files : SourceFiles}
    (distinct : (files.map Prod.fst).Nodup) {home : Module} {origin directory : SourcePath}
    {source : ModuleSource} {first second : List LoadedModule}
    (left : source.Loads files home origin directory first)
    (right : source.Loads files home origin directory second) : first = second := by
  induction left using ModuleSource.Loads.rec
    (motive_2 := fun home origin directory children modules _ =>
      ∀ other, ModuleChildrenLoad files home origin directory children other → modules = other)
    generalizing second with
  | body _ _ ih =>
    cases right with
    | body _ other => exact congrArg _ (ih _ other)
  | nil =>
    rename_i other loaded
    cases loaded
    rfl
  | inline _ _ head tail =>
    rename_i other loaded
    cases loaded with
    | inline otherHead otherTail => rw [head otherHead, tail _ otherTail]
  | external supplied _ _ head tail =>
    rename_i other loaded
    cases loaded with
    | external otherSupplied otherHead otherTail =>
      cases supplied_file_unique distinct supplied otherSupplied
      rw [head otherHead, tail _ otherTail]

theorem PackageSource.Loads.deterministic {package : PackageSource} {first second : List LoadedModule}
    (left : package.Loads first) (right : package.Loads second) : first = second := by
  obtain ⟨distinct, source, found, left⟩ := left
  obtain ⟨_, otherSource, otherFound, right⟩ := right
  cases supplied_file_unique distinct found otherFound
  exact left.deterministic distinct right

theorem PackagesLoad.deterministic {packages : List PackageSource} {first second : List LoadedModule}
    (left : PackagesLoad packages first) (right : PackagesLoad packages second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases right with
    | cons otherHead otherTail => rw [head.deterministic otherHead, ih otherTail]

theorem SourceClosure.unique {packages : List PackageSource} (first second : SourceClosure packages) :
    first = second := by
  cases first with
  | mk first included firstImports firstResolved =>
    cases second with
    | mk second other secondImports secondResolved =>
      cases included.deterministic other
      have same := Option.some.inj (firstResolved.symm.trans secondResolved)
      cases same
      rfl


theorem PackageSource.Loads.files_perm {package : PackageSource} {files : SourceFiles}
    (permuted : package.files.Perm files) {modules : List LoadedModule}
    (loaded : package.Loads modules) : ({ package with files := files }).Loads modules := by
  obtain ⟨distinct, source, found, included⟩ := loaded
  exact ⟨(permuted.map Prod.fst).nodup_iff.mp distinct, source,
    permuted.mem_iff.mp found, included.files_congr (fun _ => permuted.mem_iff)⟩

theorem PackagesLoad.reorder {packages : List PackageSource} {modules : List LoadedModule}
    (loaded : PackagesLoad packages modules) (reorder : PackageSource → SourceFiles)
    (same : ∀ package ∈ packages, package.files.Perm (reorder package)) :
    PackagesLoad (packages.map fun package => { package with files := reorder package }) modules := by
  induction loaded with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (head.files_perm (same _ (by simp)))
      (ih (fun package member => same package (by simp [member])))

def SourceClosure.reorder {packages : List PackageSource} (closure : SourceClosure packages)
    (reorder : PackageSource → SourceFiles)
    (same : ∀ package ∈ packages, package.files.Perm (reorder package)) :
    SourceClosure (packages.map fun package => { package with files := reorder package }) := by
  refine ⟨closure.modules, closure.included.reorder reorder same, closure.importBatches, ?_⟩
  simpa only [elaborateModuleImports, resolvePackageDependency.reorder] using closure.importsResolved

theorem SourceClosure.Admitted.reorder_iff {packages : List PackageSource} (closure : SourceClosure packages)
    (reorder : PackageSource → SourceFiles)
    (same : ∀ package ∈ packages, package.files.Perm (reorder package)) (program : Program) :
    (closure.reorder reorder same).Admitted program ↔ closure.Admitted program := by
  have bindings : (closure.reorder reorder same).bindingNames = closure.bindingNames := by
    funext caller home name
    have access := PackageAccess.reorder packages reorder caller.package home.package
    by_cases allowed : PackageAccess packages caller.package home.package
    · simp only [SourceClosure.bindingNames, if_pos allowed, if_pos (access.mpr allowed)]
      rfl
    · have denied : ¬PackageAccess (packages.map fun package => { package with files := reorder package })
          caller.package home.package := fun found => allowed (access.mp found)
      simp only [SourceClosure.bindingNames, if_neg allowed, if_neg denied]
  have namespaces : sourceNamespace (packages.map fun package => { package with files := reorder package }) =
      sourceNamespace packages := by
    funext caller name
    simp only [sourceNamespace, resolvePackageDependency.reorder]
  have names : (closure.reorder reorder same).functionNames = closure.functionNames := by
    simp only [SourceClosure.functionNames, namespaces, bindings]
  simp only [SourceClosure.Admitted, names]
  simp [SourceClosure.reorder, SourceClosure.homes, SourceClosure.functions, SourceClosure.imports, SourceClosure.importEntries,
    PackageSource.DependenciesValid, PackageAccess.reorder, List.map_map, Function.comp_def]


/-- Inclusion preserves package ownership and records only the original file
or an explicitly selected file from the supplied collection. -/
theorem ModuleSource.Loads.provenance {files : SourceFiles} {home : Module}
    {origin directory : SourcePath} {source : ModuleSource} {modules : List LoadedModule}
    (loaded : source.Loads files home origin directory modules) :
    ∀ node ∈ modules, node.home.package = home.package ∧
      (node.origin = origin ∨ ∃ body, (node.origin, body) ∈ files) := by
  induction loaded using ModuleSource.Loads.rec
    (motive_2 := fun home origin _ _ modules _ =>
      ∀ node ∈ modules, node.home.package = home.package ∧
        (node.origin = origin ∨ ∃ body, (node.origin, body) ∈ files)) with
  | body _ _ ih =>
    intro node member
    rcases List.mem_cons.mp member with same | member
    · subst node; exact ⟨rfl, .inl rfl⟩
    · exact ih node member
  | nil => rename_i node member; cases member
  | inline _ _ head tail =>
    rename_i node member
    rcases List.mem_append.mp member with member | member
    · exact head node member
    · exact tail node member
  | external supplied _ _ head tail =>
    rename_i node member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨owner, same | found⟩ := head node member
      · exact ⟨owner, .inr ⟨_, by rw [same]; exact supplied⟩⟩
      · exact ⟨owner, .inr found⟩
    · exact tail node member

theorem PackageSource.Loads.provenance {package : PackageSource} {modules : List LoadedModule}
    (loaded : package.Loads modules) {node : LoadedModule} (member : node ∈ modules) :
    node.home.package = package.identity ∧ ∃ source, (node.origin, source) ∈ package.files := by
  obtain ⟨_, source, supplied, included⟩ := loaded
  obtain ⟨owner, same | found⟩ := included.provenance node member
  · exact ⟨owner, source, by rw [same]; exact supplied⟩
  · exact ⟨owner, found⟩

theorem PackagesLoad.provenance {packages : List PackageSource} {modules : List LoadedModule}
    (loaded : PackagesLoad packages modules) {node : LoadedModule} (member : node ∈ modules) :
    ∃ package ∈ packages, node.home.package = package.identity ∧
      ∃ source, (node.origin, source) ∈ package.files := by
  induction loaded with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_append.mp member with first | rest
    · exact ⟨_, by simp, head.provenance first⟩
    · obtain ⟨package, included, provenance⟩ := ih rest
      exact ⟨package, by simp [included], provenance⟩


/-- The selected runtime body comes from an included module. Static source
admission constructs fresh addressed entry, then proves every actual execution
prefix safe. Neither an arbitrary caller-selected home nor a completed run is
used to supply the body's authority or permission to execute. -/
theorem SourceClosure.Admitted.function_soundness {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl}
    (selected : program.functions identity = some declaration) {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ∃ loaded ∈ closure.modules, ∃ source ∈ loaded.source.functions,
      declaration.home = loaded.home ∧
      NamedFunction.Elaborates program closure.functionNames
        ⟨source, loaded.home⟩ declaration ∧
      (∃ package ∈ packages, loaded.home.package = package.identity ∧
        ∃ fileSource, (loaded.origin, fileSource) ∈ package.files) ∧
      ∃ entry final, enterFunction heap supply declaration values = some entry ∧
        entry.activation.index = supply.next ∧ entry.supply.next = supply.next + 1 ∧
        (¬supply.Issued entry.activation) ∧
        (∀ caller callerContext owner, BindingMap.Typed program heap owner caller callerContext →
          BindingMap.Typed program entry.heap owner caller callerContext ∧
          (∀ identity ∈ entry.bindings.map Prod.snd, identity ∉ caller.map Prod.snd) ∧
          (∀ identity ∈ caller.map Prod.snd, entry.heap.read identity = heap.read identity)) ∧
        ∀ state, Run program ⟨entry, .expression declaration.body, []⟩ state →
          ConfigurationTyped program final (.one declaration.result) state ∧
          (Terminal state ∨ ∃ next, Step program state next) ∧
          AddressedEnvironment.ConsumptionFrame program final.slots entry state.outerEnvironment ∧
          (state.environment.bindings.map Prod.fst).Nodup := by
  obtain ⟨loaded, included, source, member, owner, elaborated⟩ := admitted.declaration selected
  have checked := elaborated.checked
  obtain ⟨final, body⟩ := checked.body
  obtain ⟨entry, entered, typed, activation, supplyNext, fresh, issued, _, callers⟩ :=
    enterFunction.progress arguments checked.distinct heap supply
  exact ⟨loaded, included, source, member, owner, elaborated,
    closure.included.provenance included, entry, final,
    entered, activation, supplyNext, fresh, callers,
    fun _ run => body.soundness admitted.checked typed issued run⟩


/-- Every admitted cross-package call namespace has an actual normalized
binding in the caller's own manifest, not merely a transitively supplied package. -/
theorem SourceClosure.call_dependency {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} {home : Module} {scope : SourceScope} {before after : FlowContext}
    {name : FunctionName} {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call name arguments) core type after)
    {targetHome : Module} (namespaceResolved : sourceNamespace packages home name = some targetHome)
    (foreign : targetHome.package ≠ home.package) :
    ∃ package ∈ packages, package.identity = home.package ∧
      ∃ dependency ∈ package.dependencies, dependency.target = targetHome.package ∧
        ∃ normalized, dependency.name = some normalized := by
  cases elaborated with
  | call _ selected _ _ _ =>
    obtain ⟨actual, path, access, _⟩ := closure.functionNames_selected.mp selected
    have same := Option.some.inj (path.symm.trans namespaceResolved)
    cases same
    obtain ⟨package, included, owner, same | ⟨normalized, found⟩⟩ := access
    · exact False.elim (foreign same)
    · obtain ⟨dependency, member, decoded, target⟩ := PackageSource.resolveDependency_selected found
      exact ⟨package, included, owner, dependency, member, target, normalized, decoded⟩

/-- A real dependency binding and visible candidate construct authorized
selection and source call elaboration, then the existing machine theorem proves
preservation, progress and framing for the emitted call. -/
theorem SourceClosure.Admitted.dependency_call_soundness {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {package : PackageSource} (packageIncluded : package ∈ packages) {home : Module}
    (owner : package.identity = home.package) {dependency : PackageDependency}
    (dependencyIncluded : dependency ∈ package.dependencies) {normalized spelling : Identifier}
    (decoded : dependency.name = some normalized) {children : List Identifier}
    {scope : SourceScope} {before after : FlowContext} {identity : Nat} {declaration : FunctionDecl}
    {arguments : List NamedExpr} {inputs : List Expr}
    (included : (⟨dependency.target, children⟩ : Module) ∈ closure.homes)
    (reachable : ModuleReachable closure.modules home ⟨dependency.target, children⟩)
    (candidate : VisibleFunctionCandidate closure.functions closure.imports home ⟨dependency.target, children⟩ spelling identity)
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (argumentsTyped : NamedExprsElaborate program closure.functionNames home scope before
      arguments inputs (declaration.parameters.map fun parameter => parameter.2.type) after)
    (slots : before.slots = scope.context) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) {state : Configuration}
    (run : Run program ⟨environment, .expression (.call identity inputs), []⟩ state) :
    ConfigurationTyped program after (.one declaration.result) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program after.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup := by
  have dependencies := admitted.2.1 package packageIncluded
  have selectedDependency := dependencies.resolve_existing dependencyIncluded decoded
  have allowed : PackageAccess packages home.package dependency.target :=
    ⟨package, packageIncluded, owner, .inr ⟨normalized, selectedDependency⟩⟩
  have path : sourceNamespace packages home (.qualified (.dependency normalized children) spelling) =
      some ⟨dependency.target, children⟩ := by
    simp only [sourceNamespace, FunctionName.namespace, ModulePath.resolve, ← owner,
      resolvePackageDependency.existing admitted.1 packageIncluded normalized, selectedDependency, Option.map_some]
  have base := admitted.2.2.2.1.resolve_existing included candidate
  have resolved := closure.functionNames_selected.mpr
    ⟨⟨dependency.target, children⟩, path, allowed, reachable, Grounded.functionNames.selected_iff.mp base⟩
  have elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call (.qualified (.dependency normalized children) spelling) arguments)
      (.call identity inputs) declaration.result after :=
    .call trivial resolved declared visible argumentsTyped
  exact admitted.soundness elaborated slots store issued run


theorem SourceClosure.Admitted.resolves {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program)
    {caller : Module} {name : FunctionName} {identity : Nat}
    (resolved : closure.functionNames caller name = some identity) :
    ∃ source core, closure.functions[identity]? = some source ∧ program.functions identity = some core ∧
      NamedFunction.Elaborates program closure.functionNames source core := by
  obtain ⟨_, cores, elaborated, functions⟩ := admitted.2.2.2.2
  obtain ⟨_, _, _, _, resolution⟩ := closure.functionNames_selected.mp resolved
  have base := Grounded.functionNames.selected_iff.mpr resolution
  obtain ⟨source, selected⟩ := Grounded.functionNames.selected base
  obtain ⟨core, emitted, checked⟩ := elaborated.selected selected
  exact ⟨source, core, selected, by rw [functions]; exact emitted, checked⟩

/-- Authorized aliases preserve the original declaration identity and owner.
The package guard checks the lookup namespace, not the ultimate re-exported
function's package; a valid re-export does not require an extra direct edge. -/
theorem SourceClosure.Admitted.call_resolution {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) {home : Module} {scope : SourceScope}
    {before after : FlowContext} {name : FunctionName} {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call name arguments) core type after) :
    ∃ identity declaration inputs source, closure.functions[identity]? = some source ∧
      core = .call identity inputs ∧ program.functions identity = some declaration ∧
      declaration.home = source.home ∧ declaration.visibility.Allows declaration.home home ∧
      ∃ targetHome, sourceNamespace packages home name = some targetHome ∧
        PackageAccess packages home.package targetHome.package ∧
        ModuleReachable closure.modules home targetHome ∧
        FunctionResolution closure.functions closure.imports home targetHome name.spelling identity := by
  cases elaborated with
  | call _ resolved declared visible _ =>
    obtain ⟨source, emitted, selected, found, body⟩ := admitted.resolves resolved
    have same := Option.some.inj (declared.symm.trans found)
    subst emitted
    refine ⟨_, _, _, source, selected, rfl, declared, ?_, visible,
      closure.functionNames_selected.mp resolved⟩
    cases body
    rfl

theorem SourceClosure.Admitted.evaluation_soundness {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before expression core type final)
    (slots : before.slots = scope.context) {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ AddressedEnvironment.ConsumptionFrame program final.slots environment after :=
  admitted.2.2.2.2.evaluation_soundness elaborated slots store issued evaluated

theorem SourceClosure.Admitted.correctness {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before expression core type final)
    (slots : before.slots = scope.context) (finite : FiniteCalls program core) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter → other = value ∧ otherAfter = after :=
  admitted.2.2.2.2.correctness elaborated slots finite store issued


theorem Module.child_injective {first second : Module} {left right : Identifier}
    (same : first.child left = second.child right) : first = second ∧ left = right := by
  have recovered := congrArg (fun home : Module => (home.package, home.path.dropLast)) same
  cases first
  cases second
  simp [Module.child] at recovered
  obtain ⟨rfl, rfl⟩ := recovered
  refine ⟨rfl, ?_⟩
  have paths := congrArg Module.path same
  simpa [Module.child] using paths

theorem ModuleSource.Loads.children_distinct {files : SourceFiles} {home : Module}
    {origin directory : SourcePath} {source : ModuleSource} {modules : List LoadedModule}
    (loaded : source.Loads files home origin directory modules) :
    ∀ node ∈ modules, (node.source.children.map Prod.fst).Nodup := by
  induction loaded using ModuleSource.Loads.rec
    (motive_2 := fun _ _ _ _ modules _ =>
      ∀ node ∈ modules, (node.source.children.map Prod.fst).Nodup) with
  | body distinct _ ih =>
    intro node member
    rcases List.mem_cons.mp member with same | member
    · subst node; exact distinct
    · exact ih node member
  | nil => rename_i node member; cases member
  | inline _ _ head tail | external _ _ _ head tail =>
    rename_i node member
    rcases List.mem_append.mp member with member | member
    · exact head node member
    · exact tail node member

theorem PackagesLoad.children_distinct {packages : List PackageSource} {modules : List LoadedModule}
    (loaded : PackagesLoad packages modules) {node : LoadedModule} (member : node ∈ modules) :
    (node.source.children.map Prod.fst).Nodup := by
  induction loaded with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_append.mp member with first | rest
    · obtain ⟨_, _, _, included⟩ := head
      exact included.children_distinct node first
    · exact ih rest

/-- Module traversal cannot select a different visibility for the same child.
Both module-owner uniqueness and child-name uniqueness come from actual source
admission/inclusion, not from a second independently supplied namespace table. -/
theorem SourceClosure.Admitted.child_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {parent : LoadedModule} (included : parent ∈ closure.modules)
    {name : Identifier} {visibility : Visibility} {body : Option ModuleSource}
    (declared : (name, visibility, body) ∈ parent.source.children) {caller : Module}
    (reachable : ModuleReachable closure.modules caller (parent.home.child name)) :
    visibility.Allows parent.home caller := by
  generalize targetEq : parent.home.child name = target at reachable
  cases reachable with
  | root _ =>
    have paths := congrArg Module.path targetEq
    simp [Module.child] at paths
  | child otherIncluded _ otherDeclared allowed =>
    obtain ⟨ownerEq, nameEq⟩ := Module.child_injective targetEq
    have ownerSame := unique_key_member admitted.2.2.2.1.1 included otherIncluded ownerEq
    cases ownerSame
    cases nameEq
    have declarationSame := unique_key_member (closure.included.children_distinct included)
      declared otherDeclared rfl
    cases declarationSame
    exact allowed

private theorem prefix_snoc {α : Type} {first second : List α} {last : α}
    (initial : first.IsPrefix (second ++ [last])) : first.IsPrefix second ∨ first = second ++ [last] := by
  induction second generalizing first with
  | nil =>
    cases first with
    | nil => exact .inl ⟨[], rfl⟩
    | cons head rest =>
      obtain ⟨suffix, same⟩ := initial
      have parts : head = last ∧ rest = [] ∧ suffix = [] := by simpa using same
      obtain ⟨rfl, rfl, _⟩ := parts
      exact .inr rfl
  | cons head rest ih =>
    cases first with
    | nil => exact .inl ⟨head :: rest, rfl⟩
    | cons first tail =>
      obtain ⟨suffix, same⟩ := initial
      change first :: (tail ++ suffix) = head :: (rest ++ [last]) at same
      obtain ⟨rfl, remaining⟩ := List.cons.inj same
      rcases ih ⟨suffix, remaining⟩ with shorter | equal
      · obtain ⟨suffix, same⟩ := shorter
        exact .inl ⟨suffix, congrArg (List.cons first) same⟩
      · exact .inr (congrArg (List.cons first) equal)

/-- Accessibility of a descendant retains accessibility of every enclosing
module. A longer qualifier cannot skip a hidden binding. -/
theorem ModuleReachable.ancestor {modules : List LoadedModule} {caller target : Module}
    (reachable : ModuleReachable modules caller target) {ancestor : Module}
    (packageSame : ancestor.package = target.package) (enclosing : ancestor.path.IsPrefix target.path) :
    ModuleReachable modules caller ancestor := by
  induction reachable with
  | root included =>
    obtain ⟨suffix, same⟩ := enclosing
    have parts : ancestor.path = [] ∧ suffix = [] := by simpa using same
    change ModuleReachable modules caller ⟨ancestor.package, ancestor.path⟩
    rw [parts.1, packageSame]
    exact .root included
  | @child parent name visibility body included reachable declared allowed ih =>
    rcases prefix_snoc enclosing with shorter | equal
    · exact ih packageSame shorter
    · have same : ancestor = parent.home.child name := by
        change Module.mk ancestor.package ancestor.path = Module.mk (parent.home.child name).package (parent.home.child name).path
        rw [packageSame, equal]
        rfl
      rw [same]
      exact .child included reachable declared allowed


theorem SourceClosure.Admitted.call_ancestor_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {parent : LoadedModule} (included : parent ∈ closure.modules)
    {child : Identifier} {visibility : Visibility} {body : Option ModuleSource}
    (declared : (child, visibility, body) ∈ parent.source.children)
    {home : Module} {scope : SourceScope} {before after : FlowContext}
    {name : FunctionName} {arguments : List NamedExpr} {core : Expr} {type : Ty}
    {targetHome : Module} (namespaceResolved : sourceNamespace packages home name = some targetHome)
    (packageSame : parent.home.package = targetHome.package)
    (enclosing : (parent.home.child child).path.IsPrefix targetHome.path)
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call name arguments) core type after) : visibility.Allows parent.home home := by
  cases elaborated with
  | call _ selected _ _ _ =>
    obtain ⟨actual, path, _, reachable, _⟩ := closure.functionNames_selected.mp selected
    have same := Option.some.inj (path.symm.trans namespaceResolved)
    cases same
    exact admitted.child_visibility included declared (reachable.ancestor packageSame enclosing)


/-- A failed namespace interpretation cannot fall back to a different module
or a function with the same spelling. This applies inside every source body. -/
theorem SourceClosure.call_namespace_missing {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} {home : Module} {scope : SourceScope} {before after : FlowContext}
    {name : FunctionName} {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (missing : sourceNamespace packages home name = none) :
    ¬ NamedExpr.Elaborates program closure.functionNames home scope before (.call name arguments) core type after := by
  intro elaborated
  cases elaborated with
  | call _ selected _ _ _ =>
    obtain ⟨_, path, _⟩ := closure.functionNames_selected.mp selected
    rw [missing] at path
    contradiction

theorem SourceClosure.call_super_depth {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} {home : Module} {scope : SourceScope} {before after : FlowContext}
    {additional : Nat} {children : List Identifier} {spelling : Identifier}
    {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call (.qualified (.super additional children) spelling) arguments) core type after) :
    additional + 1 ≤ home.path.length := by
  apply Classical.byContradiction
  intro beyond
  have missing := (ModulePath.resolve_super_none (resolvePackageDependency packages home.package)
    home additional children).mpr (Nat.lt_of_not_ge beyond)
  exact SourceClosure.call_namespace_missing
    (name := .qualified (.super additional children) spelling) missing elaborated

/-- The spelling actually written in a dependency-qualified call is selected
from the caller's manifest. Another alias of the same package cannot replace it. -/
theorem SourceClosure.call_dependency_spelling {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} {home : Module} {scope : SourceScope} {before after : FlowContext}
    {dependencyName spelling : Identifier} {children : List Identifier}
    {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call (.qualified (.dependency dependencyName children) spelling) arguments) core type after) :
    ∃ package ∈ packages, package.identity = home.package ∧
      ∃ dependency ∈ package.dependencies, dependency.name = some dependencyName ∧
        ModuleReachable closure.modules home ⟨dependency.target, children⟩ := by
  cases elaborated with
  | call _ selected _ _ _ =>
    obtain ⟨targetHome, path, _, reachable, _⟩ := closure.functionNames_selected.mp selected
    change (resolvePackageDependency packages home.package dependencyName).map
      (fun package => (⟨package, children⟩ : Module)) = some targetHome at path
    obtain ⟨target, selectedDependency, rfl⟩ := Option.map_eq_some_iff.mp path
    obtain ⟨package, included, owner, found⟩ := resolvePackageDependency.selected selectedDependency
    obtain ⟨dependency, member, decoded, same⟩ := PackageSource.resolveDependency_selected found
    refine ⟨package, included, owner, dependency, member, decoded, ?_⟩
    rw [same]
    exact reachable


/-- A source import constructs its unique callable declaration before argument
checking. Every typed execution prefix of that call then satisfies general
preservation, progress and storage framing. No successful lookup is an input. -/
theorem SourceClosure.Admitted.imported_call_soundness {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (sourceIncluded : source ∈ loaded.source.imports)
    {target : Module} (path : source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target)
    {edge : FunctionImport} (emitted : ImportSelection.Emits loaded.home source.visibility target source.selection (.binding edge))
    {sourceName localName : Identifier} (kind : edge.kind = .explicit sourceName localName)
    {caller : Module} {name : FunctionName}
    (namespaceResolved : sourceNamespace packages caller name = some edge.home)
    (spelling : name.spelling = localName)
    (access : PackageAccess packages caller.package edge.home.package)
    (reachable : ModuleReachable closure.modules caller edge.home)
    (bindingVisible : edge.visibility.Allows edge.home caller) :
    ∃ identity declaration, closure.functionNames caller name = some identity ∧
      program.functions identity = some declaration ∧
      ∀ {scope : SourceScope} {before after : FlowContext} {arguments : List NamedExpr} {inputs : List Expr},
        name.Unshadowed scope → declaration.visibility.Allows declaration.home caller →
        NamedExprsElaborate program closure.functionNames caller scope before arguments inputs
          (declaration.parameters.map fun parameter => parameter.2.type) after →
        before.slots = scope.context →
        ∀ {environment : Environment},
          BindingMap.Typed program environment.heap environment.activation environment.bindings before →
          environment.supply.Issued environment.activation →
          ∀ {state : Configuration}, Run program ⟨environment, .expression (.call identity inputs), []⟩ state →
            ConfigurationTyped program after (.one declaration.result) state ∧
              (Terminal state ∨ ∃ next, Step program state next) ∧
              AddressedEnvironment.ConsumptionFrame program after.slots environment state.outerEnvironment ∧
              (state.environment.bindings.map Prod.fst).Nodup := by
  have entryMember := closure.import_emitted included sourceIncluded path emitted
  have member : edge ∈ closure.imports :=
    List.mem_flatMap.mpr ⟨.binding edge, entryMember, by simp [ImportEntry.bindings]⟩
  have valid := admitted.2.2.2.1
  obtain ⟨identity, candidate⟩ := valid.explicit_binding member kind
  have selectedBinding := valid.resolve_existing (valid.2.2.1 edge member).1
    ⟨edge.visibility, candidate, bindingVisible⟩
  have selected : closure.functionNames caller name = some identity := by
    apply closure.functionNames_selected.mpr
    refine ⟨edge.home, namespaceResolved, access, reachable, ?_⟩
    rw [spelling]
    exact Grounded.functionNames.selected_iff.mp selectedBinding
  obtain ⟨_, declaration, _, declared, _⟩ := admitted.resolves selected
  refine ⟨identity, declaration, selected, declared, ?_⟩
  intro scope before after arguments inputs unshadowed visible argumentsTyped slots environment store issued state run
  have elaborated : NamedExpr.Elaborates program closure.functionNames caller scope before
      (.call name arguments) (.call identity inputs) declaration.result after :=
    .call unshadowed selected declared visible argumentsTyped
  exact admitted.soundness elaborated slots store issued run


end Grounded
