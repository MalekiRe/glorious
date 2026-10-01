import Grounded.SourceDeclarations

/-! Declaration-driven inclusion over a finite supplied collection of decoded
files. No ambient file lookup is available. Function and import ownership is
assigned by the module tree, never by a file's position in that collection.
Package identities and qualified import targets are already decoded here. -/
namespace Grounded

abbrev SourcePath := List String

inductive ModuleSource where
  | body (functions : List FunctionSyntax) (imports : List FunctionImportSyntax)
      (children : List (Identifier × Option ModuleSource))

def ModuleSource.functions : ModuleSource → List FunctionSyntax
  | .body functions _ _ => functions

def ModuleSource.imports : ModuleSource → List FunctionImportSyntax
  | .body _ imports _ => imports

abbrev SourceFiles := List (SourcePath × ModuleSource)

structure LoadedModule where
  home : Module
  origin : SourcePath
  directory : SourcePath
  source : ModuleSource

def Module.child (home : Module) (name : Identifier) : Module :=
  ⟨home.package, home.path ++ [name]⟩

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
    List (Identifier × Option ModuleSource) → List LoadedModule → Prop where
  | nil {home origin directory} : ModuleChildrenLoad files home origin directory [] []
  | inline {home origin directory name body rest first tail}
      (included : ModuleSource.Loads files (home.child name) origin
        (childDirectory directory name) body first)
      (remaining : ModuleChildrenLoad files home origin directory rest tail) :
      ModuleChildrenLoad files home origin directory ((name, some body) :: rest) (first ++ tail)
  | external {home origin directory name body rest first tail}
      (supplied : (childFile directory name, body) ∈ files)
      (included : ModuleSource.Loads files (home.child name) (childFile directory name)
        (childDirectory directory name) body first)
      (remaining : ModuleChildrenLoad files home origin directory rest tail) :
      ModuleChildrenLoad files home origin directory ((name, none) :: rest) (first ++ tail)
end

structure PackageSource where
  identity : Nat
  root : SourcePath
  files : SourceFiles

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

/-- Static module inclusion feeds the same elaboration and machine contract.
There is no independently supplied module list or declaration-owner table. -/
def SourceClosure.Admitted {packages : List PackageSource} (closure : SourceClosure packages)
    (program : Program) : Prop :=
  (packages.map PackageSource.identity).Nodup ∧
  NamedFunctionsAdmitted closure.homes closure.functions closure.imports program

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
      NamedFunction.Elaborates program (functionNames closure.functions closure.imports)
        ⟨source, loaded.home⟩ declaration := by
  obtain ⟨_, _, core, elaborated, functions⟩ := admitted.2
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
    (elaborated : NamedExpr.Elaborates program (functionNames closure.functions closure.imports)
      home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment : Environment} (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    {state : Configuration} (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup :=
  admitted.2.soundness elaborated slots store issued run


private theorem supplied_file_unique {files : SourceFiles}
    (distinct : (files.map Prod.fst).Nodup) {path : SourcePath} {first second : ModuleSource}
    (left : (path, first) ∈ files) (right : (path, second) ∈ files) : first = second := by
  induction files with
  | nil => simp at left
  | cons entry rest ih =>
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp left with same | leftTail
    · cases same
      rcases List.mem_cons.mp right with same | rightTail
      · cases same; rfl
      exact False.elim (absent (List.mem_map.mpr ⟨_, rightTail, rfl⟩))
    · rcases List.mem_cons.mp right with same | rightTail
      · cases same
        exact False.elim (absent (List.mem_map.mpr ⟨_, leftTail, rfl⟩))
      · exact ih distinct leftTail rightTail

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
  simp only [SourceClosure.Admitted, SourceClosure.reorder, SourceClosure.homes,
    SourceClosure.functions, SourceClosure.imports, List.map_map, Function.comp_def]


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
      NamedFunction.Elaborates program (functionNames closure.functions closure.imports)
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
    fun _ run => body.soundness admitted.2.checked typed issued run⟩


end Grounded
