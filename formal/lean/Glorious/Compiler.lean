import Glorious.Semantics.Manifest
import Glorious.Semantics.Transform
import Glorious.Semantics.Lower

namespace Glorious.Semantics

structure CompileRequest where
  manifest : CompilerManifest
  program : Program
  entryPackage : String
  entryPath : Path := ⟨["main"]⟩
  deriving Repr

structure CompileOutput where
  target : Target
  analyzed : AnalyzedProgram
  artifact : VM.Artifact
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
      | some path => return (← resolve program bindings implementation.header.module .trait path).declaration
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
        | .capture _ => reject .unsupportedContract "receiver reference route requires the receiving receiver-origin encoding"
      let path ← path.mapM fun projection => match projection with
        | .field index | .index index => pure index
        | _ => reject .missingEvidence "reference contract projection is not a concrete ABI field path"
      return (result, parameter, path)
    return (index, routes)
  return { artifact with exports, referenceReturns := referenceReturns.filter (! ·.2.isEmpty) }

/-- Closed source closure → resolved declarations → typed Core → specialization
and structural control transformation → one storage/control analysis → VM IR.
No source-spelling privilege or fallback to another compiler enters this path.
The VM independently checks the receiving artifact before it is published. -/
def compileParsed (request : CompileRequest) : Check CompileOutput := do
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
  let core ← elaborateProgram program bindings
  validateCoreBindings core
  let roots := (entry :: program.functions.filterMap (fun function =>
    if function.exportName.isSome then some function.header.id else none)).eraseDups
  let specialized ← monomorphize core (roots.map (fun declaration => ⟨declaration, []⟩))
  let fused ← fuseProgram specialized
  let analyzed ← analyzeProgram fused
  let artifact ← lowerProgram analyzed entry
  let artifact ← attachInterfaceMetadata analyzed artifact
  return ⟨program.target, analyzed, artifact⟩

def compileSources (manifest : CompilerManifest) (packages : List PackageInput)
    (files : List SourceFile) (entryPackage : String) (entryPath : Path := ⟨["main"]⟩) : Check CompileOutput := do
  let program ← initialProgram manifest packages
  let program ← parseFiles program files
  compileParsed ⟨manifest, program, entryPackage, entryPath⟩

end Glorious.Semantics
