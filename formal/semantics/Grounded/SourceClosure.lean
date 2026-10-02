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

/-- Validate every declared scope, including unused imports and module bindings.
The owner is the inclusion-derived module, never the supplied file path. -/
def LoadedModule.VisibilityValid (loaded : LoadedModule) : Prop :=
  (∀ declaration ∈ loaded.source.functions, declaration.visibility.ValidAt loaded.home) ∧
  (∀ source ∈ loaded.source.imports, source.visibility.ValidAt loaded.home) ∧
  (∀ child ∈ loaded.source.children, child.2.1.ValidAt loaded.home)

/-- Source imports cannot claim the driver-only automatic-priority marker. -/
def LoadedModule.Valid (loaded : LoadedModule) : Prop :=
  loaded.VisibilityValid ∧ ∀ source ∈ loaded.source.imports, source.selection.Authored


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


theorem ModuleReachable.descendant_caller {modules : List LoadedModule} {caller target child : Module}
    (reachable : ModuleReachable modules caller target) (same : child.package = caller.package)
    (enclosing : caller.path.IsPrefix child.path) : ModuleReachable modules child target := by
  induction reachable with
  | root included => exact .root included
  | child included _ declared allowed ih =>
    exact .child included ih declared (allowed.descendant same enclosing)


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
  standardPrelude : Option ModulePath := none
  noStd : Bool := false
  noImplicitPrelude : Bool := false

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

/-- The driver-selected prelude is a distinct lowest-priority import request.
Suppression affects only automatic injection, never explicit source imports. -/
def PackageSource.preludeRequest (package : PackageSource) : Option FunctionImportSyntax :=
  if package.noStd || package.noImplicitPrelude then none
  else package.standardPrelude.map fun target => ⟨target, .item .prelude, .private⟩

def resolvePackagePrelude : List PackageSource → Nat → Option FunctionImportSyntax
  | [], _ => none
  | package :: rest, owner =>
      if package.identity = owner then package.preludeRequest else resolvePackagePrelude rest owner

theorem PackageSource.preludeRequest_selected (package : PackageSource) (source : FunctionImportSyntax) :
    package.preludeRequest = some source ↔
      package.noStd = false ∧ package.noImplicitPrelude = false ∧
      ∃ target, package.standardPrelude = some target ∧ source = ⟨target, .item .prelude, .private⟩ := by
  cases first : package.noStd <;> cases second : package.noImplicitPrelude <;>
    simp [PackageSource.preludeRequest, first, second, Option.map_eq_some_iff]
  constructor
  · rintro ⟨target, chosen, same⟩; exact ⟨target, chosen, same.symm⟩
  · rintro ⟨target, chosen, same⟩; exact ⟨target, chosen, same.symm⟩

theorem resolvePackagePrelude.existing {packages : List PackageSource}
    (distinct : (packages.map PackageSource.identity).Nodup) {package : PackageSource}
    (member : package ∈ packages) :
    resolvePackagePrelude packages package.identity = package.preludeRequest := by
  induction packages with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [resolvePackagePrelude]
    · have different : head.identity ≠ package.identity := by
        intro same
        exact (List.nodup_cons.mp distinct).1 (List.mem_map.mpr ⟨package, member, same.symm⟩)
      simp only [resolvePackagePrelude, if_neg different]
      exact ih (List.nodup_cons.mp distinct).2 member

theorem resolvePackagePrelude.origin {packages : List PackageSource} {owner : Nat}
    {source : FunctionImportSyntax} (selected : resolvePackagePrelude packages owner = some source) :
    ∃ package ∈ packages, package.identity = owner ∧ package.preludeRequest = some source := by
  induction packages with
  | nil => cases selected
  | cons package rest ih =>
    simp only [resolvePackagePrelude] at selected
    split at selected
    · rename_i same
      exact ⟨package, by simp, same, selected⟩
    · obtain ⟨original, member, same, found⟩ := ih selected
      exact ⟨original, by simp [member], same, found⟩


theorem PackageSource.preludeRequest_suppressed (package : PackageSource)
    (suppressed : package.noStd = true ∨ package.noImplicitPrelude = true) :
    package.preludeRequest = none := by
  rcases suppressed with disabled | disabled <;> simp [PackageSource.preludeRequest, disabled]

theorem resolvePackagePrelude.reorder (packages : List PackageSource) (reorder : PackageSource → SourceFiles) :
    resolvePackagePrelude (packages.map fun package => { package with files := reorder package }) =
      resolvePackagePrelude packages := by
  induction packages with
  | nil => rfl
  | cons package rest ih =>
    funext owner
    by_cases same : package.identity = owner <;>
      simp [resolvePackagePrelude, PackageSource.preludeRequest, same, ih]

def LoadedModule.importRequests (packages : List PackageSource) (loaded : LoadedModule) : List FunctionImportSyntax :=
  loaded.source.imports ++ (resolvePackagePrelude packages loaded.home.package).toList

theorem LoadedModule.importRequests_origin (packages : List PackageSource) (loaded : LoadedModule)
    (source : FunctionImportSyntax) : source ∈ loaded.importRequests packages ↔
    source ∈ loaded.source.imports ∨ resolvePackagePrelude packages loaded.home.package = some source := by
  simp [LoadedModule.importRequests]

theorem LoadedModule.explicit_import_member (packages : List PackageSource) (loaded : LoadedModule)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.source.imports) :
    source ∈ loaded.importRequests packages :=
  (loaded.importRequests_origin packages source).mpr (.inl declared)


def LoadedModule.importSources (packages : List PackageSource) (loaded : LoadedModule) : List (Module × FunctionImportSyntax) :=
  (loaded.importRequests packages).map fun source => (loaded.home, source)

def elaborateModuleImports (packages : List PackageSource) (modules : List LoadedModule) : Option (List (List ImportEntry)) :=
  resolveFunctionImports (fun home => resolvePackageDependency packages home.package)
    (modules.flatMap (LoadedModule.importSources packages))


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
    {source : FunctionImportSyntax} (declared : source ∈ loaded.importRequests packages) :
    ∃ entries ∈ closure.importBatches, ∃ target,
      source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target ∧
      entries = source.selection.emit loaded.home target source.visibility := by
  have member : (loaded.home, source) ∈ closure.modules.flatMap (LoadedModule.importSources packages) :=
    List.mem_flatMap.mpr ⟨loaded, included, List.mem_map.mpr ⟨source, declared, rfl⟩⟩
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have selected : (closure.modules.flatMap (LoadedModule.importSources packages))[index]? = some (loaded.home, source) := by
    exact List.getElem?_eq_some_iff.mpr ⟨bound, same⟩
  obtain ⟨edge, found, resolved⟩ := resolveFunctionImports.source closure.importsResolved selected
  exact ⟨edge, List.mem_of_getElem? found, FunctionImportSyntax.resolve_selected resolved⟩

/-- Every binding originates in the source group's rules, with unchanged owner
and visibility. Namespace-only group entries never become candidate bindings. -/
theorem SourceClosure.import_origin {packages : List PackageSource} (closure : SourceClosure packages)
    {edge : FunctionImport} (member : edge ∈ closure.imports) :
    ∃ loaded ∈ closure.modules, ∃ source ∈ loaded.importRequests packages,
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
    {source : FunctionImportSyntax} (declared : source ∈ loaded.importRequests packages)
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
      ∀ loaded ∈ modules, ∀ source ∈ loaded.importRequests packages,
        ∃ target, source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target := by
  constructor
  · rintro ⟨closure, built⟩ loaded member source declared
    have modulesEq := SourceClosure.fromModules_selected built
    obtain ⟨_, _, target, path, _⟩ := closure.import_source (modulesEq.symm ▸ member) declared
    exact ⟨target, path⟩
  · intro paths
    have possible : ∀ owned ∈ modules.flatMap (LoadedModule.importSources packages),
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
  NamedProgramAdmitted closure.functionNames closure.functions program ∧
  ∀ loaded ∈ closure.modules, loaded.Valid

theorem SourceClosure.Admitted.root_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules) (root : loaded.home.path = []) :
    (∀ declaration ∈ loaded.source.functions, declaration.visibility ≠ .parent) ∧
    (∀ source ∈ loaded.source.imports, source.visibility ≠ .parent) ∧
    (∀ child ∈ loaded.source.children, child.2.1 ≠ .parent) := by
  have valid := (admitted.2.2.2.2.2 loaded included).1
  exact ⟨fun declaration member => (valid.1 declaration member).not_parent_at_root root,
    fun source member => (valid.2.1 source member).not_parent_at_root root,
    fun child member => (valid.2.2 child member).not_parent_at_root root⟩


theorem SourceClosure.Admitted.checked {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) : program.Checked :=
  admitted.2.2.2.2.1.checked

/-- Source admission preserves the meaning of every explicit principal class. -/
theorem SourceClosure.Admitted.principal_permission {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : DataDecl} {principal : Principal}
    (declared : program.data identity = some declaration)
    (manual : declaration.restriction = some principal) (permission : UsePermission) :
    UsePermitted program.data permission (.nominal identity) ↔ permission.Allows (some principal) :=
  admitted.checked.data.principals.permission declared manual permission

/-- A manual declaration cannot advertise permission absent from an owned field,
including a field of an inactive variant or of an unused declaration. -/
theorem SourceClosure.Admitted.no_principal_widening {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : DataDecl} {principal : Principal}
    (declared : program.data identity = some declaration)
    (manual : declaration.restriction = some principal) {permission : UsePermission}
    (promised : permission.Allows (some principal)) {schema : Fields} {field : Field}
    (variant : schema ∈ declaration.schemas) (member : field ∈ schema.residents)
    (unsupported : ¬ UsePermitted program.data permission field.type) : False := by
  have permitted := (admitted.principal_permission declared manual permission).mpr promised
  cases permitted with
  | nominal found restriction fields =>
    cases Option.some.inj (found.symm.trans declared)
    exact unsupported (fields schema variant field member)


/-- No admitted nominal declaration contains a direct or indirect inline cycle,
regardless of whether any function constructs a value of that declaration. -/
theorem SourceClosure.Admitted.no_inline_cycle {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : DataDecl} (declared : program.data identity = some declaration) :
    ¬ Relation.TransGen (InlineChild program.data) (.nominal identity) (.nominal identity) :=
  (admitted.checked.data.layouts identity declaration declared).no_inline_cycle


/-- Even unused or nonreturning function interfaces have valid decoded layouts. -/
theorem SourceClosure.Admitted.interface_layout {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl} (declared : program.functions identity = some declaration) :
    (∀ parameter ∈ declaration.parameters, FiniteLayout program.target program.data parameter.2.type) ∧
      FiniteLayout program.target program.data declaration.result := by
  have checked := admitted.checked.functions identity declaration declared
  exact ⟨checked.parametersFinite, checked.resultFinite⟩

theorem SourceClosure.Admitted.no_interface_inline_cycle {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl} (declared : program.functions identity = some declaration) :
    (∀ parameter ∈ declaration.parameters,
      ¬ Relation.TransGen (InlineChild program.data) parameter.2.type parameter.2.type) ∧
      ¬ Relation.TransGen (InlineChild program.data) declaration.result declaration.result := by
  have layouts := admitted.interface_layout declared
  exact ⟨fun parameter member => (layouts.1 parameter member).no_inline_cycle, layouts.2.no_inline_cycle⟩


/-- Every admitted alias, including an unused one, resolves to one finite type. -/
theorem SourceClosure.Admitted.alias_resolution {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {name : String} {body : TypeExpr} (declared : program.aliases name = some body) :
    ∃ type, ResolvesType program.aliases (.alias name) type ∧ FiniteLayout program.target program.data type ∧
      ∀ other, ResolvesType program.aliases (.alias name) other → other = type := by
  obtain ⟨type, expanded, finite⟩ := admitted.checked.aliases name body declared
  have resolved := ResolvesType.alias declared expanded
  exact ⟨type, resolved, finite, resolved.unique⟩

theorem SourceClosure.Admitted.no_alias_cycle {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {name : String} {body : TypeExpr} (declared : program.aliases name = some body) :
    ¬ Relation.TransGen (AliasDependency program.aliases) name name := by
  obtain ⟨type, resolved, _⟩ := admitted.alias_resolution declared
  exact resolved.no_alias_cycle

/-- Missing references in a declared alias body are rejected even when no
function uses the alias. References nested inside tuples and arrays are covered. -/
theorem SourceClosure.Admitted.no_unresolved_alias {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {name reference : String} {body : TypeExpr} (declared : program.aliases name = some body)
    (mentioned : body.MentionsAlias reference) (missing : program.aliases reference = none) : False := by
  obtain ⟨type, expanded, _⟩ := admitted.checked.aliases name body declared
  obtain ⟨definition, found⟩ := (expanded.alias_dependencies reference mentioned).1
  rw [missing] at found
  cases found


/-- Every admitted decoded constant materializes a unique typed value through
actual evaluation, preserving the caller's heap and lexical scope. Termination
is derived from structural checking, including unused declarations. -/
theorem SourceClosure.Admitted.constant_correctness {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {name : String} {declaration : ConstantDecl} {home : Module}
    (declared : program.constants name = some declaration)
    (visible : declaration.visibility.Allows declaration.home home) :
    ∃ type value, ResolvesType program.aliases declaration.type type ∧ ValueHasType program value type ∧
      ∀ environment : Environment, ∃ after,
        Evaluates program environment (.constant name) value after ∧
        after.scope = environment.scope ∧ after.heap = environment.heap ∧
        ∀ other otherAfter, Evaluates program environment (.constant name) other otherAfter →
          other = value ∧ otherAfter = after := by
  have checked := admitted.checked.constants name declaration declared
  obtain ⟨type, resolved, initialized⟩ := checked.body
  have access : HasType program home [] (.constant name) type [] :=
    .constant declared visible resolved checked.structural initialized
  obtain ⟨value, resident, runs⟩ := access.structural_value (.constant name)
  refine ⟨type, value, resolved, resident, ?_⟩
  intro environment
  obtain ⟨after, run, scope, heap⟩ := runs environment
  exact ⟨after, run, scope, heap, fun _ _ other => run.unique other⟩


/-- Import-path authorization comes from actual source admission over the
complete elaborated import product, not an independently supplied namespace. -/
theorem SourceClosure.Admitted.source_import_access {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (declared : source ∈ loaded.importRequests packages) :
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
    {source : FunctionImportSyntax} (declared : source ∈ loaded.importRequests packages)
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
  obtain ⟨_, core, elaborated, functions, _⟩ := admitted.2.2.2.2.1
  rw [functions] at selected
  obtain ⟨source, found, body⟩ := elaborated.selected_core selected
  obtain ⟨loaded, included, item, member, same⟩ := closure.function_owner (List.mem_of_getElem? found)
  subst source
  refine ⟨loaded, included, item, member, ?_, body⟩
  cases body
  rfl

theorem SourceClosure.Admitted.declaration_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl} (selected : program.functions identity = some declaration) :
    declaration.visibility.ValidAt declaration.home := by
  obtain ⟨loaded, included, source, member, _, elaborated⟩ := admitted.declaration selected
  have valid := (admitted.2.2.2.2.2 loaded included).1.1 source member
  cases elaborated
  exact valid


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
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program :=
  elaborated.soundness slots admitted.checked store issued run

/-- Source admission determines a complete behavior without a termination or
future-state premise. Infinite execution retains the same general safety contract
as finite execution, rather than being encoded as an abort. -/
theorem SourceClosure.Admitted.behavior {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program closure.functionNames
      home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    (∃ after value, Evaluates program environment core value after ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      (⟨after, .result value, []⟩ : Configuration).OwnershipSafe program ∧
      Configuration.ExternalFrame ⟨environment, .expression core, []⟩ ⟨after, .result value, []⟩ ∧
      ∀ identity, environment.heap.next ≤ identity.index → identity.index < after.heap.next →
        after.heap.Retired identity) ∨
    (∃ trace, InfiniteRun program ⟨environment, .expression core, []⟩ trace ∧
      ∀ index, ConfigurationTyped program final (.one type) (trace index) ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment (trace index).outerEnvironment ∧
        (trace index).OwnershipSafe program ∧
        Configuration.ExternalFrame ⟨environment, .expression core, []⟩ (trace index) ∧
        ∀ identity, environment.heap.next ≤ identity.index →
          ∀ cell, (trace index).environment.heap.read identity = some cell →
            ¬ (trace index).Untracked identity) :=
  (elaborated.checked slots).behavior admitted.checked store issued



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
  have requests : LoadedModule.importSources (packages.map fun package => { package with files := reorder package }) =
      LoadedModule.importSources packages := by
    funext loaded
    simp [LoadedModule.importSources, LoadedModule.importRequests, resolvePackagePrelude.reorder]
  simpa only [elaborateModuleImports, requests, resolvePackageDependency.reorder] using closure.importsResolved

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
      declaration.visibility.ValidAt declaration.home ∧
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
          (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  obtain ⟨loaded, included, source, member, owner, elaborated⟩ := admitted.declaration selected
  have checked := elaborated.checked
  obtain ⟨final, body, disposable⟩ := checked.body
  obtain ⟨entry, entered, typed, activation, supplyNext, fresh, issued, _, callers⟩ :=
    enterFunction.progress arguments checked.distinct heap supply
  exact ⟨loaded, included, source, member, owner, elaborated,
    closure.included.provenance included, admitted.declaration_visibility selected, entry, final,
    entered, activation, supplyNext, fresh, callers,
    fun _ run => body.soundness admitted.checked typed issued run⟩


/-- Source admission keeps every active and retained scope live through actual
execution. Identities retired before entry remain dead and cannot reappear in
those scopes. Surviving old cells retain their original owner and declared type. -/
theorem SourceClosure.Admitted.storage_lifetime_safety {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {identity : Nat} {declaration : FunctionDecl}
    (selected : program.functions identity = some declaration) {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ∃ entry, enterFunction heap supply declaration values = some entry ∧
      ∀ state, Run program ⟨entry, .expression declaration.body, []⟩ state →
        (∀ front back, state.continuation = front ++ back →
          ∀ address ∈ (continuationEnvironment state.environment front).bindings.map Prod.snd,
            ∃ cell, state.environment.heap.read address = some cell) ∧
        (∀ address, address.index < heap.next → ∀ cell, state.environment.heap.read address = some cell →
          ∃ old, heap.read address = some old ∧ cell.activation = old.activation ∧ cell.type = old.type) ∧
        ∀ address, heap.Retired address → state.environment.heap.Retired address ∧
          ∀ front back, state.continuation = front ++ back →
            address ∉ (continuationEnvironment state.environment front).bindings.map Prod.snd := by
  obtain ⟨_, _, _, _, _, _, _, _, entry, final, entered, _, _, _, _, safe⟩ :=
    admitted.function_soundness selected arguments heap supply
  obtain ⟨inputs, _, representation⟩ := Option.map_eq_some_iff.mp entered
  have entryHistory : RuntimeHeap.History heap entry.heap := by
    rw [← representation]
    exact allocateBindings.history _ _ _
  have entryOld : ∀ address, address.index < heap.next → entry.heap.read address = heap.read address := by
    rw [← representation]
    exact fun _ allocated => allocateBindings.old _ _ _ allocated
  refine ⟨entry, entered, ?_⟩
  intro state run
  have typed := (safe state run).1
  refine ⟨typed.live_scopes, ?_, ?_⟩
  · intro address allocated cell found
    obtain ⟨old, original, owner, type⟩ :=
      run.storage_origin (Nat.lt_of_lt_of_le allocated entryHistory.next_le) found
    exact ⟨old, (entryOld address allocated).symm.trans original, owner, type⟩
  · intro address retired
    have dead := retired.history (entryHistory.trans run.heap_history)
    exact ⟨dead, fun _ _ split => typed.retired_not_retained dead split⟩


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

/-- Candidate access is transported through actual source elaboration to the
runtime declaration. Alias visibility cannot replace original authority. -/
theorem SourceClosure.Admitted.candidate_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {caller home : Module} {name : Identifier} {identity : Nat}
    (candidate : VisibleFunctionCandidate closure.functions closure.imports caller home name identity)
    {declaration : FunctionDecl} (declared : program.functions identity = some declaration) :
    declaration.visibility.Allows declaration.home caller := by
  obtain ⟨_, cores, elaborated, functions, _⟩ := admitted.2.2.2.2.1
  rw [functions] at declared
  obtain ⟨origin, found, body⟩ := elaborated.selected_core declared
  have authorized := candidate.origin_access found
  cases body
  exact authorized

theorem SourceClosure.Admitted.resolved_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {caller : Module} {name : FunctionName} {identity : Nat}
    (selected : closure.functionNames caller name = some identity)
    {declaration : FunctionDecl} (declared : program.functions identity = some declaration) :
    declaration.visibility.Allows declaration.home caller := by
  obtain ⟨_, _, _, _, resolution⟩ := closure.functionNames_selected.mp selected
  exact admitted.candidate_visibility resolution.1 declared

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

    (argumentsTyped : NamedExprsElaborate program closure.functionNames home scope before
      arguments inputs (declaration.parameters.map fun parameter => parameter.2.type) after)
    (slots : before.slots = scope.context) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) {state : Configuration}
    (run : Run program ⟨environment, .expression (.call identity inputs), []⟩ state) :
    ConfigurationTyped program after (.one declaration.result) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program after.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
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
    .call trivial resolved declared (admitted.candidate_visibility candidate declared) argumentsTyped
  exact admitted.soundness elaborated slots store issued run


theorem SourceClosure.Admitted.resolves {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program)
    {caller : Module} {name : FunctionName} {identity : Nat}
    (resolved : closure.functionNames caller name = some identity) :
    ∃ source core, closure.functions[identity]? = some source ∧ program.functions identity = some core ∧
      NamedFunction.Elaborates program closure.functionNames source core := by
  obtain ⟨_, cores, elaborated, functions, _⟩ := admitted.2.2.2.2.1
  obtain ⟨_, _, _, _, resolution⟩ := closure.functionNames_selected.mp resolved
  have base := Grounded.functionNames.selected_iff.mpr resolution
  obtain ⟨source, selected, _⟩ := Grounded.functionNames.selected base
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
  admitted.2.2.2.2.1.evaluation_soundness elaborated slots store issued evaluated

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
  admitted.2.2.2.2.1.correctness elaborated slots finite store issued


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
    {source : FunctionImportSyntax} (sourceIncluded : source ∈ loaded.importRequests packages)
    {target : Module} (path : source.target.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target)
    {edge : FunctionImport} (emitted : ImportSelection.Emits loaded.home source.visibility target source.selection (.binding edge))
    {sourceName localName : Identifier} (kind : edge.kind = .explicit sourceName localName)
    {caller : Module} {name : FunctionName}
    (namespaceResolved : sourceNamespace packages caller name = some edge.home)
    (spelling : name.spelling = localName)
    (access : PackageAccess packages caller.package edge.home.package)
    (reachable : ModuleReachable closure.modules caller edge.home)
    (bindingVisible : edge.visibility.Allows edge.home caller) :
    ∃ identity declaration, program.functions identity = some declaration ∧
      (closure.functionNames caller name = some identity ↔ declaration.visibility.Allows declaration.home caller) ∧
      declaration.visibility.Allows declaration.home edge.home ∧
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
              (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  have entryMember := closure.import_emitted included sourceIncluded path emitted
  have member : edge ∈ closure.imports :=
    List.mem_flatMap.mpr ⟨.binding edge, entryMember, by simp [ImportEntry.bindings]⟩
  have valid := admitted.2.2.2.1
  obtain ⟨identity, candidate, origin, originSelected, originVisible⟩ := valid.explicit_binding member kind
  obtain ⟨_, cores, bodies, functions, _⟩ := admitted.2.2.2.2.1
  obtain ⟨declaration, coreSelected, elaborated⟩ := bodies.selected originSelected
  have declared : program.functions identity = some declaration := by rw [functions]; exact coreSelected
  have visibilityEq : declaration.visibility = origin.visibility ∧ declaration.home = origin.home := by
    cases elaborated
    exact ⟨rfl, rfl⟩
  have authorized : declaration.visibility.Allows declaration.home edge.home := by
    simpa only [visibilityEq.1, visibilityEq.2] using originVisible
  have select : declaration.visibility.Allows declaration.home caller →
      closure.functionNames caller name = some identity := by
    intro visible
    have originalAccess : FunctionAccess closure.functions identity caller :=
      ⟨origin, originSelected, by simpa only [visibilityEq.1, visibilityEq.2] using visible⟩
    have selectedBinding := valid.resolve_existing (valid.2.2.1 edge member).1
      ⟨edge.visibility, candidate, bindingVisible, originalAccess⟩
    apply closure.functionNames_selected.mpr
    refine ⟨edge.home, namespaceResolved, access, reachable, ?_⟩
    rw [spelling]
    exact Grounded.functionNames.selected_iff.mp selectedBinding
  refine ⟨identity, declaration, declared, ⟨fun selected => admitted.resolved_visibility selected declared, select⟩, authorized, ?_⟩
  intro scope before after arguments inputs unshadowed visible argumentsTyped slots environment store issued state run
  have elaborated : NamedExpr.Elaborates program closure.functionNames caller scope before
      (.call name arguments) (.call identity inputs) declaration.result after :=
    .call unshadowed (select visible) declared visible argumentsTyped
  exact admitted.soundness elaborated slots store issued run


/-- Inclusion, not a future resolver result, supplies local namespace access. -/
theorem ModuleSource.Loads.self_reachable {whole : List LoadedModule}
    (valid : ∀ node ∈ whole, node.VisibilityValid)
    {files : SourceFiles} {home : Module} {origin directory : SourcePath}
    {source : ModuleSource} {modules : List LoadedModule} (loaded : source.Loads files home origin directory modules) :
    (∀ node ∈ modules, node ∈ whole) → ModuleReachable whole home home →
    ∀ node ∈ modules, ModuleReachable whole node.home node.home := by
  induction loaded using ModuleSource.Loads.rec
    (motive_2 := fun home _ _ children modules _ =>
      (∀ node ∈ modules, node ∈ whole) →
      (∀ child ∈ children, ModuleReachable whole (home.child child.1) (home.child child.1)) →
      ∀ node ∈ modules, ModuleReachable whole node.home node.home) with
  | @body home origin directory functions imports children descendants _ _ ih =>
    intro subset reachable node member
    rcases List.mem_cons.mp member with same | member
    · subst node; exact reachable
    · apply ih (fun other found => subset other (.tail _ found)) ?_ node member
      intro child declared
      have parentIncluded : (⟨home, origin, directory, .body functions imports children⟩ : LoadedModule) ∈ whole :=
        subset _ (.head _)
      have scope := (valid _ parentIncluded).2.2 child declared
      exact .child parentIncluded (reachable.descendant_caller rfl ⟨[child.1], rfl⟩) declared
        ((show child.2.1.Allows home home from scope).descendant rfl ⟨[child.1], rfl⟩)
  | nil => rename_i _ _ node member; cases member
  | inline _ _ head tail | external _ _ _ head tail =>
    rename_i subset edges node member
    rcases List.mem_append.mp member with first | rest
    · exact head (fun other found => subset other (List.mem_append.mpr (.inl found)))
        (edges _ (.head _)) node first
    · exact tail (fun other found => subset other (List.mem_append.mpr (.inr found)))
        (fun child found => edges child (.tail _ found)) node rest

theorem ModuleSource.Loads.root_member {files : SourceFiles} {home : Module}
    {origin directory : SourcePath} {source : ModuleSource} {modules : List LoadedModule}
    (loaded : source.Loads files home origin directory modules) :
    (⟨home, origin, directory, source⟩ : LoadedModule) ∈ modules := by
  cases loaded
  exact .head _

theorem PackagesLoad.self_reachable {whole : List LoadedModule}
    (valid : ∀ node ∈ whole, node.VisibilityValid)
    {packages : List PackageSource} {modules : List LoadedModule} (loaded : PackagesLoad packages modules) :
    (∀ node ∈ modules, node ∈ whole) → ∀ node ∈ modules, ModuleReachable whole node.home node.home := by
  induction loaded with
  | nil => intro _ node member; cases member
  | @cons package packages first rest head tail ih =>
    intro subset node member
    rcases List.mem_append.mp member with first | rest
    · obtain ⟨_, source, _, tree⟩ := head
      have contained := fun other found => subset other (List.mem_append.mpr (.inl found))
      have root : (⟨package.identity, []⟩ : Module) ∈ whole.map LoadedModule.home :=
        List.mem_map.mpr ⟨_, contained _ tree.root_member, rfl⟩
      exact tree.self_reachable valid contained (.root root) node first
    · exact ih (fun other found => subset other (List.mem_append.mpr (.inr found))) node rest

theorem SourceClosure.Admitted.self_reachable {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules) :
    ModuleReachable closure.modules loaded.home loaded.home :=
  closure.included.self_reachable (fun loaded member => (admitted.2.2.2.2.2 loaded member).1)
    (fun _ member => member) loaded included

/-- A resolved local identity receives namespace access from source inclusion,
not from a separately assumed access table. -/
theorem SourceClosure.Admitted.local_selected {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules) {name : Identifier} {identity : Nat}
    (selected : Grounded.functionNames closure.functions closure.imports loaded.home loaded.home name = some identity) :
    closure.functionNames loaded.home (.unqualified name) = some identity := by
  obtain ⟨package, packageIncluded, owner, _⟩ := closure.included.provenance included
  exact closure.functionNames_selected.mpr ⟨loaded.home, rfl,
    ⟨package, packageIncluded, owner.symm, .inl rfl⟩, admitted.self_reachable included,
    Grounded.functionNames.selected_iff.mp selected⟩


/-- Bare callable lookup derives namespace access from the actual source closure. -/
theorem SourceClosure.Admitted.local_resolution {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules) {name : Identifier} {identity : Nat}
    (candidate : VisibleFunctionCandidate closure.functions closure.imports loaded.home loaded.home name identity) :
    closure.functionNames loaded.home (.unqualified name) = some identity := by
  have selected := admitted.2.2.2.1.resolve_existing (List.mem_map.mpr ⟨loaded, included, rfl⟩) candidate
  exact admitted.local_selected included selected



theorem LoadedModule.importRequests_suppressed {packages : List PackageSource}
    (distinct : (packages.map PackageSource.identity).Nodup) {package : PackageSource}
    (member : package ∈ packages) (loaded : LoadedModule) (owner : package.identity = loaded.home.package)
    (suppressed : package.noStd = true ∨ package.noImplicitPrelude = true) :
    loaded.importRequests packages = loaded.source.imports := by
  unfold LoadedModule.importRequests
  rw [← owner, resolvePackagePrelude.existing distinct member, package.preludeRequest_suppressed suppressed]
  simp

/-- Every automatic-priority edge comes from the enabled driver-selected
prelude, never from an authored item, group or nested import. -/
theorem SourceClosure.Admitted.automatic_import_origin {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {edge : FunctionImport} (member : edge ∈ closure.imports) (automatic : edge.kind = .prelude) :
    ∃ loaded ∈ closure.modules, ∃ package ∈ packages, ∃ path,
      edge.home = loaded.home ∧ package.identity = loaded.home.package ∧
      package.noStd = false ∧ package.noImplicitPrelude = false ∧
      package.standardPrelude = some path ∧ edge.visibility = .private ∧
      path.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some edge.target := by
  obtain ⟨loaded, included, source, requested, home, visibility, target, resolved, emitted⟩ := closure.import_origin member
  rcases (loaded.importRequests_origin packages source).mp requested with authored | generated
  · exact False.elim (((admitted.2.2.2.2.2 loaded included).2 source authored).emitted_kind emitted automatic)
  · obtain ⟨package, packageIncluded, owner, selected⟩ := resolvePackagePrelude.origin generated
    obtain ⟨enabled, implicitEnabled, path, profile, same⟩ := (package.preludeRequest_selected source).mp selected
    subst source
    cases emitted
    exact ⟨loaded, included, package, packageIncluded, path, rfl, owner,
      enabled, implicitEnabled, profile, rfl, resolved⟩

/-- Each module has one driver-selected automatic edge, independent of source
file order and repeated provenance paths. Uniqueness is derived from package
identity, the selected profile and actual path resolution. -/
theorem SourceClosure.Admitted.automatic_import_unique {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {first second : FunctionImport} (firstMember : first ∈ closure.imports) (secondMember : second ∈ closure.imports)
    (firstKind : first.kind = .prelude) (secondKind : second.kind = .prelude)
    (same : first.home = second.home) : first = second := by
  obtain ⟨left, _, leftPackage, leftIncluded, leftPath, leftHome, leftOwner, _, _, leftProfile, leftVisibility, leftResolved⟩ :=
    admitted.automatic_import_origin firstMember firstKind
  obtain ⟨right, _, rightPackage, rightIncluded, rightPath, rightHome, rightOwner, _, _, rightProfile, rightVisibility, rightResolved⟩ :=
    admitted.automatic_import_origin secondMember secondKind
  have homes : left.home = right.home := leftHome.symm.trans (same.trans rightHome)
  have owners : leftPackage.identity = rightPackage.identity :=
    leftOwner.trans ((congrArg Module.package homes).trans rightOwner.symm)
  have packagesSame := unique_key_member admitted.1 leftIncluded rightIncluded owners
  cases packagesSame
  cases Option.some.inj (leftProfile.symm.trans rightProfile)
  rw [homes] at leftResolved
  have targets := Option.some.inj (leftResolved.symm.trans rightResolved)
  have kinds := firstKind.trans secondKind.symm
  have visibilities := leftVisibility.trans rightVisibility.symm
  cases first
  cases second
  cases same
  cases targets
  cases kinds
  cases visibilities
  rfl


/-- Automatic prelude lookup consumes lowest-priority selection. Explicit and
authored-glob bindings suppress it before argument checking; invocation checks
original declaration's visibility. The resulting call uses general soundness. -/
theorem SourceClosure.Admitted.prelude_call_soundness {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {package : PackageSource} (packageIncluded : package ∈ packages)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules) (owner : package.identity = loaded.home.package)
    {path : ModulePath} (profile : package.standardPrelude = some path)
    (enabled : package.noStd = false) (implicitEnabled : package.noImplicitPrelude = false)
    {target : Module} (pathResolved : path.resolve (resolvePackageDependency packages loaded.home.package) loaded.home = some target)
    {name : Identifier} {identity : Nat}
    (unshadowed : ¬ ExplicitFunctionBinding closure.functions closure.imports loaded.home name)
    (noGlob : ¬ GlobFunctionBinding closure.functions closure.imports loaded.home name)
    (candidate : VisibleFunctionCandidate closure.functions closure.imports loaded.home target name identity) :
    ∃ declaration, closure.functionNames loaded.home (.unqualified name) = some identity ∧
      program.functions identity = some declaration ∧
      ∀ {scope : SourceScope} {before after : FlowContext} {arguments : List NamedExpr} {inputs : List Expr},
        scope.resolve name = none →
        NamedExprsElaborate program closure.functionNames loaded.home scope before arguments inputs
          (declaration.parameters.map fun parameter => parameter.2.type) after →
        before.slots = scope.context →
        ∀ {environment : Environment},
          BindingMap.Typed program environment.heap environment.activation environment.bindings before →
          environment.supply.Issued environment.activation →
          ∀ {state : Configuration}, Run program ⟨environment, .expression (.call identity inputs), []⟩ state →
            ConfigurationTyped program after (.one declaration.result) state ∧
              (Terminal state ∨ ∃ next, Step program state next) ∧
              AddressedEnvironment.ConsumptionFrame program after.slots environment state.outerEnvironment ∧
              (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  let source : FunctionImportSyntax := ⟨path, .item .prelude, .private⟩
  have request : resolvePackagePrelude packages loaded.home.package = some source := by
    rw [← owner, resolvePackagePrelude.existing admitted.1 packageIncluded]
    simp [PackageSource.preludeRequest, enabled, implicitEnabled, profile, source]
  have sourceIncluded := (loaded.importRequests_origin packages source).mpr (.inr request)
  let edge : FunctionImport := ⟨loaded.home, target, .prelude, .private⟩
  have entryMember : .binding edge ∈ closure.importEntries :=
    closure.import_emitted included sourceIncluded pathResolved (.item .prelude)
  have member : edge ∈ closure.imports :=
    List.mem_flatMap.mpr ⟨.binding edge, entryMember, by simp [ImportEntry.bindings]⟩
  have targetIncluded := (admitted.2.2.2.1.2.2.1 edge member).2.1
  have resolvedTarget := admitted.2.2.2.1.resolve_existing targetIncluded candidate
  have selectedCore := Grounded.functionNames.prelude_without_glob member rfl rfl
    (by simp [edge, Visibility.Allows]) unshadowed noGlob
    (Grounded.functionNames.selected_iff.mp resolvedTarget)
    (fun other otherMember same kind => admitted.automatic_import_unique otherMember member kind rfl same)
  have selected := admitted.local_selected included selectedCore
  obtain ⟨_, declaration, _, declared, _⟩ := admitted.resolves selected
  refine ⟨declaration, selected, declared, ?_⟩
  intro scope before after arguments inputs lexical argumentsTyped slots environment store issued state run
  have elaborated : NamedExpr.Elaborates program closure.functionNames loaded.home scope before
      (.call (.unqualified name) arguments) (.call identity inputs) declaration.result after :=
    .call lexical selected declared (admitted.resolved_visibility selected declared) argumentsTyped
  exact admitted.soundness elaborated slots store issued run


/-- Authored imports are validated at declaration time; generated prelude
requests have private visibility by construction. Both feed the same product. -/
theorem SourceClosure.Admitted.import_request_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {loaded : LoadedModule} (included : loaded ∈ closure.modules)
    {source : FunctionImportSyntax} (member : source ∈ loaded.importRequests packages) :
    source.visibility.ValidAt loaded.home := by
  rcases (loaded.importRequests_origin packages source).mp member with authored | automatic
  · exact (admitted.2.2.2.2.2 loaded included).1.2.1 source authored
  · obtain ⟨package, _, _, selected⟩ := resolvePackagePrelude.origin automatic
    obtain ⟨_, _, target, _, rfl⟩ := (package.preludeRequest_selected source).mp selected
    simp [Visibility.ValidAt, Visibility.Allows]


/-- Already-evaluated arguments enter the real call frame. Normal completion
includes callee retirement and restoration of the caller's scope; divergence
keeps every pending continuation well typed. Lookup supplies call authority. -/
theorem SourceClosure.Admitted.invocation_behavior {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {caller : Module} {name : FunctionName} {identity : Nat}
    (selected : closure.functionNames caller name = some identity)
    {declaration : FunctionDecl} (declared : program.functions identity = some declaration)
    {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map fun parameter => parameter.2.type))
    {context : FlowContext} {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) :
    declaration.visibility.Allows declaration.home caller ∧
    ((∃ after value, Run program ⟨environment, .results values, [.call declaration]⟩ ⟨after, .result value, []⟩ ∧
      ValueHasType program value declaration.result ∧ after.scope = environment.scope ∧
      BindingMap.Typed program after.heap after.activation after.bindings context ∧
      AddressedEnvironment.ConsumptionFrame program context.slots environment after ∧
      (⟨after, .result value, []⟩ : Configuration).OwnershipSafe program ∧
      Configuration.ExternalFrame ⟨environment, .results values, [.call declaration]⟩ ⟨after, .result value, []⟩ ∧
      (∀ identity, after.heap.read identity = environment.heap.read identity) ∧
      (∀ identity, environment.heap.next ≤ identity.index → identity.index < after.heap.next →
        after.heap.Retired identity) ∧
      ∃ inputs, prepareBindings declaration.parameters values = some inputs ∧
        ∀ identity ∈ (enterBindings environment.heap environment.supply inputs).bindings.map Prod.snd,
          after.heap.Retired identity) ∨
    (∃ trace, InfiniteRun program ⟨environment, .results values, [.call declaration]⟩ trace ∧
      ∀ index, ConfigurationTyped program context (.one declaration.result) (trace index) ∧
        AddressedEnvironment.ConsumptionFrame program context.slots environment (trace index).outerEnvironment ∧
        (trace index).OwnershipSafe program ∧
        Configuration.ExternalFrame ⟨environment, .results values, [.call declaration]⟩ (trace index) ∧
        (∀ identity cell, environment.heap.read identity = some cell →
          (trace index).environment.heap.read identity = some cell) ∧
        ∀ identity, environment.heap.next ≤ identity.index →
          ∀ cell, (trace index).environment.heap.read identity = some cell →
            ¬ (trace index).Untracked identity)) := by
  refine ⟨admitted.resolved_visibility selected declared, ?_⟩
  have entry : ConfigurationTyped program context (.one declaration.result)
      ⟨environment, .results values, [.call declaration]⟩ :=
    .intro store issued (.results arguments) (.cons (.call declared) .nil)
  rcases entry.behavior admitted.checked with ⟨after, value, run, typed, stored, framed, safe, external, retired⟩ | ⟨trace, infinite, safe⟩
  · refine .inl ⟨after, value, run, typed, run.outer_scope, stored, framed, safe, external,
      run.call_heap ?_, retired, run.call_cleanup⟩
    intro identity member
    obtain ⟨cell, found⟩ := store.live identity member
    exact environment.heap.bounded _ _ found
  · refine .inr ⟨trace, infinite, ?_⟩
    intro index
    obtain ⟨typed, framed, owned, external, tracked⟩ := safe index
    exact ⟨typed, framed, owned, external, fun _ _ found => (infinite.prefix index).call_frame found, tracked⟩

/-- Ordered Copy/move inputs and complete invocation share one pre-state
compatibility contract. Actual inputs retain their original observations; no
intermediate readiness, supplied argument values or callee termination is assumed. -/
theorem SourceClosure.Admitted.compatible_call_behavior {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {home : Module} {name : FunctionName} {identity : Nat}
    (selected : closure.functionNames home name = some identity)
    {declaration : FunctionDecl} (declared : program.functions identity = some declaration)
    {before : FlowContext} {inputs : List (Expr × Ty)}
    (arguments : inputs.map Prod.snd = declaration.parameters.map fun parameter => parameter.2.type)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home before.slots left.1 right.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.1 = .read place ∨ input.1 = .move place)
    (inputsAdmitted : ∀ input ∈ inputs, ∃ after, HasType program home before input.1 input.2 after)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ final middle values bindings,
      HasType program home before (.call identity (inputs.map Prod.fst)) declaration.result final ∧
      EvaluatesMany program environment (inputs.map Prod.fst) values middle ∧
      values.map some = inputs.map (fun input => input.1.inputObservation program environment) ∧
      prepareBindings declaration.parameters values = some bindings ∧
      Run program ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      (∀ state, Run program
          ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ state →
        ∀ identity cell, middle.heap.read identity = some cell → state.environment.heap.read identity = some cell) ∧
      ((∃ after value, Evaluates program environment (.call identity (inputs.map Prod.fst)) value after ∧
        ValueHasType program value declaration.result ∧
        BindingMap.Typed program after.heap after.activation after.bindings final ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
        (⟨after, .result value, []⟩ : Configuration).OwnershipSafe program ∧
        Configuration.ExternalFrame ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩
          ⟨after, .result value, []⟩ ∧
        (∀ identity, after.heap.read identity = middle.heap.read identity) ∧
        (∀ identity, environment.heap.next ≤ identity.index → identity.index < after.heap.next →
          after.heap.Retired identity) ∧
        ∀ identity ∈ (enterBindings middle.heap middle.supply bindings).bindings.map Prod.snd,
          after.heap.Retired identity) ∨
      (∃ trace, InfiniteRun program ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩ trace ∧
        ∀ index, ConfigurationTyped program final (.one declaration.result) (trace index) ∧
          AddressedEnvironment.ConsumptionFrame program final.slots environment (trace index).outerEnvironment ∧
          (trace index).OwnershipSafe program ∧
          Configuration.ExternalFrame ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩ (trace index) ∧
          ∀ identity, environment.heap.next ≤ identity.index →
            ∀ cell, (trace index).environment.heap.read identity = some cell →
              ¬ (trace index).Untracked identity)) := by
  obtain ⟨final, middle, values, bindings, checked, evaluated, observed, prepared, entered, typed, _⟩ :=
    HasType.compatible_call_entry admitted.checked declared (admitted.resolved_visibility selected declared)
      arguments compatible ordinary inputsAdmitted store issued
  refine ⟨final, middle, values, bindings, checked, evaluated, observed, prepared, entered, ?_, ?_⟩
  · intro state suffix identity cell found
    exact (Run.step (Step.callInputs prepared) suffix).call_frame found
  rcases typed.behavior admitted.checked with ⟨after, value, returned, resident, stored, _, safe, _, _⟩ | ⟨trace, infinite, _⟩
  · have run := entered.trans returned
    have framed := (checked.soundness admitted.checked store issued run).2.2.1
    have bounded : ∀ identity ∈ environment.bindings.map Prod.snd, identity.index < environment.heap.next := by
      intro identity member
      obtain ⟨cell, found⟩ := store.live identity member
      exact environment.heap.bounded _ _ found
    refine .inl ⟨after, value, run, resident, stored, framed, safe, run.external_frame,
      (Run.step (Step.callInputs prepared) returned).call_heap ?_,
      run.return_retires_all bounded, returned.body_return_retires⟩
    intro identity member
    have same : middle.bindings = environment.bindings :=
      congrArg AddressedScope.bindings evaluated.outer_scope
    exact Nat.lt_of_lt_of_le (bounded identity (by simpa only [same] using member)) evaluated.heap_history.next_le
  · obtain ⟨whole, execution⟩ := entered.prepend_infinite infinite
    refine .inr ⟨whole, execution, ?_⟩
    intro index
    have safe := checked.soundness admitted.checked store issued (execution.prefix index)
    exact ⟨safe.1, safe.2.2.1, safe.2.2.2.2, (execution.prefix index).external_frame,
      fun _ fresh _ live => (execution.prefix index).allocated_tracked fresh live⟩


end Grounded
