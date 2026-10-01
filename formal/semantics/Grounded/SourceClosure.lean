import Grounded.SourceDeclarations

/-! Declaration-driven inclusion over a finite supplied collection of decoded
files. No ambient file lookup is available. Function and import ownership is
assigned by the module tree, never by a file's position in that collection.
Package identities and qualified import targets are already decoded here. -/
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

structure SourceClosure (packages : List PackageSource) where
  modules : List LoadedModule
  included : PackagesLoad packages modules

def SourceClosure.homes {packages : List PackageSource} (closure : SourceClosure packages) : List Module :=
  closure.modules.map LoadedModule.home

def LoadedModule.functions (loaded : LoadedModule) : List NamedFunction :=
  loaded.source.functions.map fun source => ⟨source, loaded.home⟩

def LoadedModule.imports (loaded : LoadedModule) : List FunctionImport :=
  loaded.source.imports.map fun source => ⟨source, loaded.home⟩

def SourceClosure.functions {packages : List PackageSource} (closure : SourceClosure packages) : List NamedFunction :=
  closure.modules.flatMap LoadedModule.functions

def SourceClosure.imports {packages : List PackageSource} (closure : SourceClosure packages) : List FunctionImport :=
  closure.modules.flatMap LoadedModule.imports

/-- Package authorization guards the existing unique-identity resolver.
Import traversal and function-body elaboration retain their shared producers. -/
noncomputable def SourceClosure.functionNames {packages : List PackageSource}
    (closure : SourceClosure packages) (caller home : Module) (name : Identifier) : Option Nat := by
  classical
  exact if PackageAccess packages caller.package home.package
    then if ModuleReachable closure.modules caller home
      then Grounded.functionNames closure.functions closure.imports caller home name else none
    else none

theorem SourceClosure.functionNames_selected {packages : List PackageSource} (closure : SourceClosure packages)
    {caller home : Module} {name : Identifier} {identity : Nat} :
    closure.functionNames caller home name = some identity ↔
      PackageAccess packages caller.package home.package ∧
      ModuleReachable closure.modules caller home ∧
        FunctionResolution closure.functions closure.imports caller home name identity := by
  classical
  simp only [SourceClosure.functionNames]
  split
  · split <;> simp_all [Grounded.functionNames.selected_iff]
  · simp_all


/-- Static module inclusion feeds the same elaboration and machine contract.
There is no independently supplied module list or declaration-owner table. -/
def SourceClosure.Admitted {packages : List PackageSource} (closure : SourceClosure packages)
    (program : Program) : Prop :=
  (packages.map PackageSource.identity).Nodup ∧
  (∀ package ∈ packages, package.DependenciesValid packages) ∧
  (∀ edge ∈ closure.imports, PackageAccess packages edge.home.package edge.target.package ∧
    ModuleReachable closure.modules edge.home edge.target) ∧
  FunctionImportsValid closure.homes closure.functions closure.imports ∧
  NamedProgramAdmitted closure.functionNames closure.functions program

theorem SourceClosure.Admitted.checked {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program) : program.Checked :=
  admitted.2.2.2.2.checked

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
  | mk first included =>
    cases second with
    | mk second other =>
      cases included.deterministic other
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
    SourceClosure (packages.map fun package => { package with files := reorder package }) :=
  ⟨closure.modules, closure.included.reorder reorder same⟩

theorem SourceClosure.Admitted.reorder_iff {packages : List PackageSource} (closure : SourceClosure packages)
    (reorder : PackageSource → SourceFiles)
    (same : ∀ package ∈ packages, package.files.Perm (reorder package)) (program : Program) :
    (closure.reorder reorder same).Admitted program ↔ closure.Admitted program := by
  have names : (closure.reorder reorder same).functionNames = closure.functionNames := by
    funext caller home name
    have access := PackageAccess.reorder packages reorder caller.package home.package
    by_cases allowed : PackageAccess packages caller.package home.package
    · simp only [SourceClosure.functionNames, if_pos allowed, if_pos (access.mpr allowed)]
      rfl
    · have denied : ¬PackageAccess (packages.map fun package => { package with files := reorder package })
          caller.package home.package := fun found => allowed (access.mp found)
      simp only [SourceClosure.functionNames, if_neg allowed, if_neg denied]
  simp only [SourceClosure.Admitted, names]
  simp [SourceClosure.reorder, SourceClosure.homes, SourceClosure.functions, SourceClosure.imports,
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
    (foreign : (name.owner home).package ≠ home.package) :
    ∃ package ∈ packages, package.identity = home.package ∧
      ∃ dependency ∈ package.dependencies, dependency.target = (name.owner home).package ∧
        ∃ normalized, dependency.name = some normalized := by
  cases elaborated with
  | call _ selected _ _ _ =>
    obtain ⟨package, included, owner, same | ⟨normalized, found⟩⟩ :=
      (closure.functionNames_selected.mp selected).1
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
    (dependencyIncluded : dependency ∈ package.dependencies) {name : FunctionName}
    (target : dependency.target = (name.owner home).package)
    {scope : SourceScope} {before after : FlowContext} {identity : Nat} {declaration : FunctionDecl}
    {arguments : List NamedExpr} {inputs : List Expr}
    (included : name.owner home ∈ closure.homes)
    (reachable : ModuleReachable closure.modules home (name.owner home))
    (candidate : VisibleFunctionCandidate closure.functions closure.imports home (name.owner home) name.spelling identity)
    (unshadowed : name.Unshadowed scope) (declared : program.functions identity = some declaration)
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
  obtain ⟨normalized, decoded⟩ := (dependencies.2 dependency dependencyIncluded).1
  have selectedDependency := dependencies.resolve_existing dependencyIncluded decoded
  have allowed : PackageAccess packages home.package (name.owner home).package :=
    ⟨package, packageIncluded, owner, .inr ⟨normalized, selectedDependency.trans (congrArg some target)⟩⟩
  have base := admitted.2.2.2.1.resolve_existing included candidate
  have resolved := closure.functionNames_selected.mpr ⟨allowed, reachable, Grounded.functionNames.selected_iff.mp base⟩
  have elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call name arguments) (.call identity inputs) declaration.result after :=
    .call unshadowed resolved declared visible argumentsTyped
  exact admitted.soundness elaborated slots store issued run


theorem SourceClosure.Admitted.resolves {packages : List PackageSource} {closure : SourceClosure packages}
    {program : Program} (admitted : closure.Admitted program)
    {caller home : Module} {name : Identifier} {identity : Nat}
    (resolved : closure.functionNames caller home name = some identity) :
    ∃ source core, closure.functions[identity]? = some source ∧ program.functions identity = some core ∧
      NamedFunction.Elaborates program closure.functionNames source core := by
  obtain ⟨_, cores, elaborated, functions⟩ := admitted.2.2.2.2
  have base := Grounded.functionNames.selected_iff.mpr (closure.functionNames_selected.mp resolved).2.2
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
      PackageAccess packages home.package (name.owner home).package ∧
      ModuleReachable closure.modules home (name.owner home) ∧
      FunctionResolution closure.functions closure.imports home (name.owner home) name.spelling identity := by
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

theorem SourceClosure.Admitted.call_child_visibility {packages : List PackageSource}
    {closure : SourceClosure packages} {program : Program} (admitted : closure.Admitted program)
    {parent : LoadedModule} (included : parent ∈ closure.modules)
    {child : Identifier} {visibility : Visibility} {body : Option ModuleSource}
    (declared : (child, visibility, body) ∈ parent.source.children)
    {home : Module} {scope : SourceScope} {before after : FlowContext}
    {name : FunctionName} {arguments : List NamedExpr} {core : Expr} {type : Ty}
    (target : name.owner home = parent.home.child child)
    (elaborated : NamedExpr.Elaborates program closure.functionNames home scope before
      (.call name arguments) core type after) : visibility.Allows parent.home home := by
  cases elaborated with
  | call _ selected _ _ _ =>
    have reachable := (closure.functionNames_selected.mp selected).2.1
    rw [target] at reachable
    exact admitted.child_visibility included declared reachable


end Grounded
