import Glorious.Compiler

namespace Glorious.Driver

open Semantics System

structure Options where
  input : Option String := none
  output : Option String := none
  manifest : Option String := none
  package : String := "main"
  entry : Path := ⟨["main"]⟩
  dependencies : List PackageInput := []
  emitJson : Bool := false
  assembler : String := "target/debug/examples/assemble_semantic_artifact"
  help : Bool := false
  deriving Repr

def usage : String :=
  "glorious-lean SOURCE.glorious [-o OUTPUT.grbc] [--manifest FILE.json]\n" ++
  "  [--package NAME] [--entry PATH] [--dependency NAME=ROOT.glorious]\n" ++
  "  [--emit-json] [--assembler PATH]\n\n" ++
  "The manifest supplies the target, package closure and exact runtime bindings.\n" ++
  "Without one, compilation uses the VM64 profile with no intrinsic/host authority.\n" ++
  "--emit-json emits unchecked receiving IR; normal output is independently VM-verified.\n"

def parseOptions : List String → Options → Check Options
  | [], options => return options
  | "--help" :: rest, options | "-h" :: rest, options => parseOptions rest { options with help := true }
  | "--emit-json" :: rest, options => parseOptions rest { options with emitJson := true }
  | "-o" :: value :: rest, options | "--output" :: value :: rest, options => parseOptions rest { options with output := some value }
  | "--manifest" :: value :: rest, options => parseOptions rest { options with manifest := some value }
  | "--package" :: value :: rest, options => parseOptions rest { options with package := value.replace "-" "_" }
  | "--entry" :: value :: rest, options => parseOptions rest { options with entry := ⟨value.splitOn "::"⟩ }
  | "--assembler" :: value :: rest, options => parseOptions rest { options with assembler := value }
  | "--dependency" :: value :: rest, options => do
    match value.splitOn "=" with
    | [name, path] => parseOptions rest { options with
      dependencies := options.dependencies ++
        [⟨name.replace "-" "_", path, []⟩] }
    | _ => reject .invalidSource "--dependency expects NAME=ROOT.glorious"
  | value :: rest, options => do
    require (!value.startsWith "-" && options.input.isNone) .invalidSource s!"unexpected command-line argument {value}"
    parseOptions rest { options with input := some value }

def checkedIO (result : Check α) : IO α :=
  match result with
  | .ok value => pure value
  | .error diagnostic => throw (IO.userError s!"{repr diagnostic.problem} at source {diagnostic.span.file}:{diagnostic.span.start}: {diagnostic.message}")

structure SourceClosure where
  initial : Program
  program : Program
  files : List SourceFile := []
  parsed : Spec.Source.ParsedFiles initial files program
  nextId : Id := 1

def parseSource (closure : SourceClosure) (module : ModuleId) (path : FilePath) : IO SourceClosure := do
  let bytes ← IO.FS.readBinFile path
  let file : SourceFile := ⟨closure.files.length, module, path.toString, bytes⟩
  let result ← checkedIO (Spec.parseOneCertified closure.program closure.nextId file)
  return { initial := closure.initial, program := result.val.2, files := closure.files ++ [file],
    parsed := closure.parsed.append (.cons result.property .nil), nextId := result.val.1 }

def childSourcePath (packages : List PackageInput) (module : ModuleId) : IO FilePath := do
  let package ← checkedIO (getRequired packages[module.packageId]? .unknownName "module package root is unavailable")
  let root : FilePath := package.rootFile
  let parent := root.parent.getD (FilePath.mk ".")
  let relative := module.path.foldl (fun path part => path / part) parent
  let direct := relative.withExtension "glorious"
  let name ← checkedIO (getRequired module.path.getLast? .unknownName "child source path is empty")
  let nested := relative / s!"{name}.glorious"
  let directExists ← direct.pathExists
  let nestedExists ← nested.pathExists
  if directExists && nestedExists then
    throw (IO.userError s!"ambiguous declared module source: {direct} and {nested}")
  if directExists then return direct
  if nestedExists then return nested
  throw (IO.userError s!"missing declared module source: {direct} or {nested}")

/-- Filesystem discovery is only the closure explicitly declared by parsed
modules and supplied package roots. Parsing is the producer of that relation;
the driver does not scan source text for module-looking names. -/
def loadSourceClosure (manifest : CompilerManifest) (packages : List PackageInput) : IO SourceClosure := do
  let program ← checkedIO (initialProgram manifest packages)
  let roots ← packages.zipIdx.foldlM (init := ({ initial := program, program, parsed := .nil } : SourceClosure)) fun closure (package, id) =>
    parseSource closure ⟨id, []⟩ package.rootFile
  let rec expand : Nat → SourceClosure → IO SourceClosure
    | 0, _ => throw (IO.userError "source module closure exceeded the declared limit")
    | fuel + 1, closure => do
      let missing := closure.program.modules.flatMap (·.children) |>.filter fun child =>
        !(closure.program.modules.any (fun module => module.identity == child))
      match missing.head? with
      | none => return closure
      | some module =>
        let path ← childSourcePath packages module
        expand fuel (← parseSource closure module path)
  expand manifest.limits.elaboration roots

structure ParsedRequest where
  request : CompileRequest
  initial : Program
  files : List SourceFile
  parsed : Spec.Source.ParsedFiles initial files request.program

def prepareRequest (options : Options) : IO ParsedRequest := do
  let manifest ← match options.manifest with
    | none => pure emptyManifest
    | some path => checkedIO (decodeManifest (← IO.FS.readFile path))
  let packages ← match options.input with
    | some input =>
      let root : PackageInput := ⟨options.package, input, (manifest.packages ++ options.dependencies).map (·.name)⟩
      pure (root :: (manifest.packages ++ options.dependencies).filter (·.name != options.package))
    | none =>
      if manifest.packages.isEmpty then throw (IO.userError "missing source root; use --help")
      pure manifest.packages
  let closure ← loadSourceClosure manifest packages
  return ⟨⟨manifest, closure.program, options.package, options.entry⟩, closure.initial, closure.files, closure.parsed⟩

def publish (options : Options) (input : ParsedRequest) (output : CompileOutput input.request) : IO Unit := do
  let json := (output.artifact.json output.target).compress
  let destination := options.output.getD (if options.emitJson then "out.grbc.json" else "out.grbc")
  if options.emitJson then
    IO.FS.writeFile destination (json ++ "\n")
  else
    let child ← do
      let (stdin, child) ← (← IO.Process.spawn {
        cmd := options.assembler, args := #["--output", destination],
        stdin := .piped, stdout := .inherit, stderr := .inherit }).takeStdin
      stdin.putStr json
      stdin.flush
      pure child
    let code ← child.wait
    unless code == 0 do throw (IO.userError s!"receiving VM verification/encoding failed (exit {code}); no successful compiler artifact was published")

def run (arguments : List String) : IO UInt32 := do
  try
    let options ← checkedIO (parseOptions arguments {})
    if options.help then IO.print usage; return 0
    let input ← prepareRequest options
    let output ← match compileParsed input.request with
      | .ok output => pure output
      | .error diagnostic =>
        let path := input.files[diagnostic.span.file]?.map (·.path) |>.getD "<semantic input>"
        throw (IO.userError s!"{path}:{diagnostic.span.start}-{diagnostic.span.stop}: {repr diagnostic.problem}: {diagnostic.message}")
    publish options input output
    return 0
  catch error =>
    IO.eprintln s!"glorious-lean: {error}"
    return 1

end Glorious.Driver
