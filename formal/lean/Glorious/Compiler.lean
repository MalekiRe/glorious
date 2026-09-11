import Glorious.Semantics.Manifest
import Glorious.Semantics.Transform
import Glorious.Semantics.Lower
import Glorious.Proof.Passes

namespace Glorious.Semantics

structure CompileRequest where
  manifest : CompilerManifest
  program : Program
  entryPackage : String
  entryPath : Path := ⟨["main"]⟩
  deriving Repr

def resolveDeclarationHeads (program : Program) (bindings : List Binding) : Check Program := do
  let fixities ← program.fixities.mapM fun fixity => do
    match fixity.targetPath with
    | none => return fixity
    | some path =>
      let binding ← resolve program bindings fixity.module .value path
      return { fixity with target := binding.declaration, targetPath := none }
  let implementations ← program.implementations.mapM fun implementation => do
    let traitDecl ← match implementation.traitPath with
      | none => pure implementation.traitDecl
      | some path => pure (← resolve program bindings implementation.header.module .trait path).declaration
    let trait ← getRequired (program.traitDecl traitDecl) .unknownName "implementation trait is unavailable"
    let methods ← implementation.methods.mapM fun (_, declaration) => do
      let function ← getRequired (program.function declaration) .unknownName "implementation method has no declaration"
      let member ← getRequired (trait.members.find? (fun member => member.header.name == function.header.name && member.signature.isSome))
        .unknownName "implementation method is not declared by the selected trait" function.header.span
      return (member.header.id, declaration)
    return { implementation with traitDecl, traitPath := none, methods }
  return { program with fixities, implementations }

def validateEntry (program : Program) (entry : DeclId) : Check Unit := do
  let function ← getRequired (program.function entry) .unknownName "entry path is not an ordinary function"
  require (function.body.isSome && function.signature.generics.isEmpty && function.signature.arguments.isEmpty)
    .incompatibleABI "executable entry must have a body and take no generic or value arguments" function.header.span
  require (!function.signature.unsafeCall && function.signature.abi == .glorious)
    .incompatibleABI "executable entry must use the safe Glorious calling convention" function.header.span
  require (function.signature.effects == .row [] []) .missingEffect "executable entry has unhandled outward effects" function.header.span

def attachInterfaceMetadata (analyzed : AnalyzedProgram) (artifact : VM.Artifact) : Check VM.Artifact := do
  let functions := analyzed.core.functions
  let exports ← analyzed.core.source.functions.filterMap (fun function =>
    function.exportName.map (function.header.id, ·)) |>.mapM fun (declaration, name) => do
      let index ← getRequired (functions.findIdx? (fun function => function.declaration == declaration))
        .malformedCore "exported declaration has no runtime specialization"
      let function ← getRequired artifact.functions[index]? .malformedCore "export references a missing VM function"
      return (name, index, function.signature)
  let referenceReturns ← analyzed.functions.zipIdx |>.mapM fun (facts, index) => do
    let routes ← facts.referenceReturns.mapM fun (result, input, path) => do
      let parameter ← match input with
        | .argument parameter => pure parameter
        | .capture _ | .receiver => reject .unsupportedContract "receiver reference route requires the receiving receiver-origin encoding"
      let path ← path.mapM fun projection => match projection with
        | .field index | .index index => pure index
        | _ => reject .missingEvidence "reference contract projection is not a concrete ABI field path"
      return (result, parameter, path)
    return (index, routes)
  return { artifact with exports, referenceReturns := referenceReturns.filter (! ·.2.isEmpty) }

structure PreparedProgram where
  program : Program
  bindings : List Binding
  entry : DeclId
  deriving Repr

def prepareProgram (request : CompileRequest) : Check PreparedProgram := do
  validateTarget request.manifest.target
  let program ← addManifestPrelude request.manifest request.program
  validatePackages program
  let bindings ← resolveImports program
  let program ← resolveDeclarationHeads program bindings
  let program ← resolveProgramTerms program bindings
  let program ← bindRuntimeManifest request.manifest program bindings
  validateFixities program
  validateCoherence program
  let package ← getRequired (program.packages.find? (fun package => package.name == request.entryPackage))
    .unknownName "entry package is not in the supplied source closure"
  let entry := (← resolve program bindings package.root .value request.entryPath).declaration
  validateEntry program entry
  return ⟨program, bindings, entry⟩

theorem prepareProgram_sound (request : CompileRequest) (prepared : PreparedProgram)
    (accepted : prepareProgram request = .ok prepared) :
    Spec.Prepared request.manifest request.program prepared.program prepared.bindings := by
  unfold prepareProgram at accepted
  constructor
  all_goals simp_all [validateCoherence, validatePackages, validateEntry, bindRuntimeManifest]

theorem interfaceMetadata_sound (analyzed : AnalyzedProgram) (entry : DeclId) (before after : VM.Artifact)
    (proof : Spec.Target.Correct analyzed.core entry before)
    (accepted : attachInterfaceMetadata analyzed before = .ok after) :
    Spec.Target.Correct analyzed.core entry after := by
  unfold attachInterfaceMetadata at accepted
  cases proof
  constructor
  all_goals simp_all [Spec.Target.System, Spec.Target.Initial, Spec.Target.WellFormed]

/-- A successful output cannot be constructed without the semantic chain.
These fields are erased only after Lean has checked them. -/
structure CompileOutput (request : CompileRequest) where
  prepared : PreparedProgram
  preparation : Spec.Prepared request.manifest request.program prepared.program prepared.bindings
  elaborated : CoreProgram
  elaboration : Spec.ElaborationCorrect prepared.program elaborated
  analyzed : AnalyzedProgram
  transformation : Glorious.Proof.Preserves (Spec.CoreSystem elaborated prepared.entry)
    (Spec.CoreSystem analyzed.core prepared.entry)
  analysis : Spec.AnalysisCorrect analyzed.core prepared.entry analyzed
  artifact : VM.Artifact
  lowering : Spec.Target.Correct analyzed.core prepared.entry artifact

def CompileOutput.target (output : CompileOutput request) : Target := output.prepared.program.target

theorem CompileOutput.preserves (output : CompileOutput request) :
    Glorious.Proof.Preserves (Spec.CoreSystem output.elaborated output.prepared.entry)
      (Spec.Target.System output.analyzed.core.source output.artifact) :=
  output.transformation.trans output.lowering.behavior

theorem CompileOutput.targetSafe (output : CompileOutput request) :
    (Spec.Target.System output.analyzed.core.source output.artifact).Safe :=
  output.lowering.behavior.safety output.analysis.valid.progress

instance : Repr (CompileOutput request) where
  reprPrec output _ := repr (output.target, output.analyzed, output.artifact)

/-- Source declarations → resolved declarations → certified Core → certified
transformation → certified shared analysis → certified VM IR. There is no
unchecked compileParsed branch behind the public driver. -/
def compileParsed (request : CompileRequest) : Check (CompileOutput request) := do
  let prepared ← match accepted : prepareProgram request with
    | .error error => .error error
    | .ok prepared => pure (⟨prepared, prepareProgram_sound request prepared accepted⟩ :
        { prepared : PreparedProgram // Spec.Prepared request.manifest request.program prepared.program prepared.bindings })
  let core ← Spec.elaborateCertified prepared.val.program prepared.val.bindings prepared.property.declarations
  validateCoreBindings core.value
  let roots := (prepared.val.entry :: prepared.val.program.functions.filterMap (fun function =>
    if function.exportName.isSome then some function.header.id else none)).eraseDups
  have entryRoot : prepared.val.entry ∈ roots := by simp [roots]
  let specialized ← Spec.monomorphizeCertified core.value roots
  let fused ← Spec.fuseCertified specialized.val roots
  let analyzed ← Spec.analyzeCertified fused.val prepared.val.entry (fused.property.roots _ entryRoot)
  let artifact ← Spec.lowerCertified fused.val prepared.val.entry analyzed
  let published ← match accepted : attachInterfaceMetadata analyzed.val artifact.val with
    | .error error => .error error
    | .ok result => pure (⟨result, interfaceMetadata_sound analyzed.val prepared.val.entry artifact.val result
        (by simpa [analyzed.property.exactInput] using artifact.property) accepted⟩ :
        { result : VM.Artifact // Spec.Target.Correct analyzed.val.core prepared.val.entry result })
  return {
    prepared := prepared.val, preparation := prepared.property,
    elaborated := core.value, elaboration := core.sound,
    analyzed := analyzed.val,
    transformation := by
      simpa [analyzed.property.exactInput] using
        (specialized.property.entryPreserved _ entryRoot).trans (fused.property.entryPreserved _ entryRoot),
    analysis := by simpa [analyzed.property.exactInput] using analyzed.property,
    artifact := published.val, lowering := published.property }

structure SourceCompileOutput (manifest : CompilerManifest) (packages : List PackageInput)
    (files : List SourceFile) (entryPackage : String) (entryPath : Path) where
  initial : Program
  initialized : initialProgram manifest packages = .ok initial
  program : Program
  parsed : Spec.Source.ParsedFiles initial files program
  output : CompileOutput ⟨manifest, program, entryPackage, entryPath⟩

def compileSources (manifest : CompilerManifest) (packages : List PackageInput)
    (files : List SourceFile) (entryPackage : String) (entryPath : Path := ⟨["main"]⟩) :
    Check (SourceCompileOutput manifest packages files entryPackage entryPath) := do
  let initial ← match accepted : initialProgram manifest packages with
    | .error error => .error error
    | .ok initial => pure (⟨initial, accepted⟩ : { initial : Program // initialProgram manifest packages = .ok initial })
  let parsed ← Spec.parseCertified initial.val files
  let output ← compileParsed ⟨manifest, parsed.val, entryPackage, entryPath⟩
  return ⟨initial.val, initial.property, parsed.val, parsed.property, output⟩

end Glorious.Semantics
