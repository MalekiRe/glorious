import Lean.Data.Json
import Glorious.Semantics.Parser
import Glorious.Semantics.Elaborate

namespace Glorious.Semantics

open Lean

structure PackageInput where
  name : String
  rootFile : String
  dependencies : List String := []
  deriving Repr

structure ImportSelector where
  package : String
  path : Path
  kind : LeafKind
  arguments : List String
  output : String
  effects : String := "!{}"
  unsafeCall : Bool := false
  abi : ABI := .glorious
  capability : Option String := none
  allocationDomain : Option Id := none
  symbol : String
  primitive : Option String := none
  retainedCallback : Bool := false
  replayable : Bool := false
  deriving Repr

structure CompilerManifest where
  identity : String
  target : Target
  packages : List PackageInput := []
  imports : List ImportSelector := []
  capabilities : List String := []
  prelude : Option (String × Path) := none
  limits : Limits := {}
  deriving Repr

def vm64Target : Target := {
  triple := "grandiose-vm64", pointerBits := 64, littleEndian := true,
  scalarAlignments := [
    (.integer false .w8, 1), (.integer true .w8, 1),
    (.integer false .w16, 2), (.integer true .w16, 2),
    (.integer false .w32, 4), (.integer true .w32, 4),
    (.integer false .w64, 8), (.integer true .w64, 8),
    (.integer false .w128, 16), (.integer true .w128, 16),
    (.integer false .pointer, 8), (.integer true .pointer, 8),
    (.floating .w32, 4), (.floating .w64, 8), (.character, 4)],
  maxObjectSize := 2 ^ 63 - 1, abiGeneration := 1,
  layoutIdentity := "grandiose-vm64-v1", callableConvention := 1,
  intrinsicManifest := "empty-v1", cEnabled := false }

def emptyManifest : CompilerManifest := { identity := "empty-v1", target := vm64Target }

def jsonField (value : Json) (field : String) : Check Json :=
  match value.getObjVal? field with
  | .ok field => .ok field
  | .error message => reject .invalidSource message

def jsonOptional (value : Json) (field : String) : Option Json :=
  match value.getObjVal? field with | .ok .null => none | .ok value => some value | .error _ => none

def jsonString (value : Json) : Check String :=
  match value.getStr? with | .ok value => .ok value | .error message => reject .invalidSource message

def jsonNat (value : Json) : Check Nat :=
  match value.getNat? with | .ok value => .ok value | .error message => reject .invalidSource message

def jsonBool (value : Json) : Check Bool :=
  match value.getBool? with | .ok value => .ok value | .error message => reject .invalidSource message

def jsonList (value : Json) : Check (List Json) :=
  match value.getArr? with | .ok value => .ok value.toList | .error message => reject .invalidSource message

def jsonDefault (value : Json) (field : String) (parse : Json → Check α) (fallback : α) : Check α :=
  match jsonOptional value field with | none => return fallback | some value => parse value

def jsonStrings (value : Json) : Check (List String) := jsonList value >>= List.mapM jsonString

def decodePackageInput (json : Json) : Check PackageInput := do
  return {
    name := (← jsonField json "name" >>= jsonString).replace "-" "_",
    rootFile := ← jsonField json "root" >>= jsonString,
    dependencies := ← jsonDefault json "dependencies" jsonStrings [] }

def decodeImportSelector (json : Json) : Check ImportSelector := do
  let kind ← jsonField json "kind" >>= jsonString
  let kind ← getRequired (lookup kind [("scalar", LeafKind.scalar), ("memory", .memory),
    ("layout", .layout), ("static", .staticData), ("host", .host), ("foreign", .foreign)])
    .missingImport "unknown runtime leaf category"
  let abi ← jsonDefault json "abi" jsonString "glorious"
  require (["glorious", "C"].contains abi) .incompatibleABI "unknown runtime calling convention"
  return {
    package := (← jsonField json "package" >>= jsonString).replace "-" "_",
    path := ⟨(← jsonField json "path" >>= jsonString).splitOn "::"⟩,
    kind, arguments := ← jsonField json "arguments" >>= jsonStrings,
    output := ← jsonField json "output" >>= jsonString,
    effects := ← jsonDefault json "effects" jsonString "!{}",
    unsafeCall := ← jsonDefault json "unsafe" jsonBool false,
    abi := if abi == "C" then .c else .glorious,
    capability := ← (jsonOptional json "capability").mapM jsonString,
    allocationDomain := ← (jsonOptional json "allocation_domain").mapM jsonNat,
    symbol := ← jsonField json "symbol" >>= jsonString,
    primitive := ← (jsonOptional json "primitive").mapM jsonString,
    retainedCallback := ← jsonDefault json "retained_callback" jsonBool false,
    replayable := ← jsonDefault json "replayable" jsonBool false }

def decodeTarget (json : Json) (manifest : String) : Check Target := do
  let pointerBits ← jsonField json "pointer_bits" >>= jsonNat
  let target := vm64Target
  let alignments ← match jsonOptional json "scalar_alignments" with
    | none => pure (target.scalarAlignments.map fun (scalar, alignment) => match scalar with
        | .integer _ .pointer => (scalar, pointerBits / 8) | _ => (scalar, alignment))
    | some json => do
      (← jsonList json).mapM fun entry => do
        let name ← jsonField entry "type" >>= jsonString
        let scalar ← getRequired (parseScalarType name) .invalidLayout "unknown scalar alignment key"
        return (scalar, ← jsonField entry "alignment" >>= jsonNat)
  let target := { target with
    pointerBits, scalarAlignments := alignments,
    triple := ← jsonField json "triple" >>= jsonString,
    littleEndian := ← jsonField json "little_endian" >>= jsonBool,
    maxObjectSize := ← jsonField json "max_object_size" >>= jsonNat,
    abiGeneration := ← jsonField json "abi_generation" >>= jsonNat,
    layoutIdentity := ← jsonField json "layout_identity" >>= jsonString,
    callableConvention := ← jsonField json "callable_convention" >>= jsonNat,
    intrinsicManifest := manifest,
    cEnabled := ← jsonDefault json "c_enabled" jsonBool false }
  validateTarget target
  return target

def decodeManifest (text : String) : Check CompilerManifest := do
  let json ← match Json.parse text with | .ok value => pure value | .error message => reject .invalidSource message
  let identity ← jsonField json "identity" >>= jsonString
  require (!identity.isEmpty) .missingImport "runtime manifest requires an explicit identity"
  let target ← decodeTarget (← jsonField json "target") identity
  let packages ← jsonDefault json "packages" (fun json => jsonList json >>= List.mapM decodePackageInput) []
  let imports ← jsonDefault json "imports" (fun json => jsonList json >>= List.mapM decodeImportSelector) []
  let capabilities ← jsonDefault json "capabilities" jsonStrings []
  let prelude ← (jsonOptional json "prelude").mapM fun value => do
    return (← jsonField value "package" >>= jsonString,
      ⟨(← jsonField value "path" >>= jsonString).splitOn "::"⟩)
  let limits : Limits ← match jsonOptional json "limits" with
    | none => pure ({} : Limits)
    | some value => do
      let default : Limits := {}
      pure ({
        normalization := ← jsonDefault value "normalization" jsonNat default.normalization,
        solving := ← jsonDefault value "solving" jsonNat default.solving,
        elaboration := ← jsonDefault value "elaboration" jsonNat default.elaboration,
        analysis := ← jsonDefault value "analysis" jsonNat default.analysis,
        alternatives := ← jsonDefault value "alternatives" jsonNat default.alternatives,
        layout := ← jsonDefault value "layout" jsonNat default.layout,
        execution := ← jsonDefault value "execution" jsonNat default.execution } : Limits)
  return { identity, target, packages, imports, capabilities, prelude, limits }

def initialProgram (manifest : CompilerManifest) (packages : List PackageInput) : Check Program := do
  let names := packages.map (·.name)
  require (unique names) .duplicate "duplicate supplied package name"
  let packages ← packages.zipIdx |>.mapM fun (package, id) => do
    let dependencies ← package.dependencies.mapM fun dependency =>
      getRequired (names.findIdx? (· == dependency.replace "-" "_")) .unknownName "declared package dependency is not in the supplied closure"
    return (⟨id, package.name, dependencies, ⟨id, []⟩⟩ : Package)
  return {
    packages, modules := [], dataTypes := [], aliases := [], traits := [], implementations := [],
    effects := [], functions := [], constants := [], fixities := [], target := manifest.target,
    imports := [], grantedCapabilities := manifest.capabilities, limits := manifest.limits }

def addManifestPrelude (manifest : CompilerManifest) (program : Program) : Check Program := do
  match manifest.prelude with
  | none => return program
  | some (name, path) =>
    let package ← getRequired (program.packages.find? (·.name == name)) .missingImport "prelude package is absent"
    let path := Path.mk (package.name :: path.components)
    let modules := program.modules.map fun moduleDecl =>
      if moduleDecl.noImplicitPrelude then moduleDecl else
        { moduleDecl with
          imports := moduleDecl.imports ++
          [⟨moduleDecl.identity, path, .value, none, true, true, false, true, {}⟩] }
    return { program with modules }

def parseManifestTerm (program : Program) (bindings : List Binding) (module : ModuleId)
    (text : String) (kind : Kind) : Check Term := do
  let file : SourceFile := ⟨0, module, "<runtime-manifest>", text.toUTF8⟩
  let tokens ← lex file
  let state : ParserState := { tokens, module, program }
  let (term, state) ← (parseTerm program.limits.normalization kind).run state
  require (state.tokens[state.position]?.map (·.kind) == some .eof)
    .incompatibleABI "trailing syntax in runtime manifest type"
  resolveTerm program bindings module program.limits.normalization term

def bindRuntimeManifest (manifest : CompilerManifest) (program : Program) (bindings : List Binding) : Check Program := do
  require (manifest.identity == program.target.intrinsicManifest) .incompatibleABI "runtime manifest and selected target differ"
  let imports ← manifest.imports.mapM fun selector => do
    let package ← getRequired (program.packages.find? (·.name == selector.package)) .missingImport "runtime selector package is absent"
    let binding ← resolve program bindings package.root .value selector.path
    let function ← getRequired (program.function binding.declaration) .missingImport "runtime selector does not name an ordinary declaration"
    require (function.header.id.packageId == package.id) .missingImport "runtime selector re-exports a declaration from a different package"
    let signature : Signature := {
      arguments := ← selector.arguments.mapM (fun text => parseManifestTerm program bindings function.header.module text .type),
      output := ← parseManifestTerm program bindings function.header.module selector.output .type,
      effects := ← parseManifestTerm program bindings function.header.module selector.effects .row,
      unsafeCall := selector.unsafeCall, abi := selector.abi }
    return ({
      identity := function.header.id, signature, kind := selector.kind,
      capability := selector.capability, allocationDomain := selector.allocationDomain,
      retainedCallback := selector.retainedCallback, replayable := selector.replayable,
      symbol := selector.symbol, primitive := selector.primitive } : RuntimeImport)
  require (unique (imports.map (·.identity))) .duplicate "several runtime roles select the same declaration"
  let functions := program.functions.map fun function =>
    if imports.any (fun binding => binding.identity == function.header.id) then
      { function with runtimeBinding := some function.header.id } else function
  let program := { program with functions, imports }
  admitImports program {}
  return program

end Glorious.Semantics
