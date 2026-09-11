import Glorious.Semantics.Transform
import Glorious.Semantics.Lower
import Glorious.Proof.Source
import Glorious.Proof.Target

/-! Mandatory proof interfaces for the executable compiler. Each theorem is
indexed by the exact successful result of the real phase. There is no alternate
test compiler, success-as-specification predicate, or permissive fallback.

This is the first proof pass. Unfinished tactic goals are build errors, not
admitted propositions; the compiler importing this module cannot be published
until every obligation checks in Lean. -/
namespace Glorious.Semantics.Spec

structure Prepared (manifest : CompilerManifest) (source result : Program)
    (bindings : List Binding) : Prop where
  target : result.target = manifest.target
  capabilities : result.grantedCapabilities = manifest.capabilities
  declarations : ProgramWellFormed result
  sourceIdentity : ∀ function ∈ source.functions,
    ∃ prepared ∈ result.functions, prepared.header = function.header ∧ prepared.body = function.body
  noInventedOrdinary : ∀ prepared ∈ result.functions,
    prepared.body.isSome = true → ∃ function ∈ source.functions, prepared.header = function.header
  bindingAuthority : ∀ binding ∈ bindings, DeclarationHeader result binding.authority ∧
    binding.declaration = binding.authority.id
  runtimeAuthority : ∀ binding ∈ result.imports,
    ∃ selector ∈ manifest.imports, selector.kind = binding.kind ∧ selector.symbol = binding.symbol ∧
      selector.primitive = binding.primitive ∧ selector.capability = binding.capability ∧
      selector.allocationDomain = binding.allocationDomain

structure TransformationCorrect (before after : CoreProgram) (roots : List DeclId) : Prop where
  declarations : before.source = after.source
  entryPreserved : ∀ entry ∈ roots, Glorious.Proof.Preserves (CoreSystem before entry) (CoreSystem after entry)
  noSourceAuthority : after.bindings = before.bindings
  roots : ∀ entry ∈ roots, ∃ function ∈ after.functions, function.declaration = entry

inductive RepresentsHead : ValueHead → ValueHead → Prop where
  | known {head} : RepresentsHead head head
  | unknown {head identity} : RepresentsHead (.symbolic identity) head

mutual
inductive RepresentsValue : Value → Value → Prop where
  | value {abstract concrete}
      (type : abstract.type = concrete.type)
      (principal : abstract.capability = concrete.capability)
      (hook : abstract.dropHook = concrete.dropHook)
      (head : RepresentsHead abstract.head concrete.head)
      (fields : RepresentsValueFields abstract.fields concrete.fields) :
      RepresentsValue abstract concrete

inductive RepresentsValueFields : List (Option Value) → List (Option Value) → Prop where
  | nil : RepresentsValueFields [] []
  | vacant {left right} (tail : RepresentsValueFields left right) :
      RepresentsValueFields (none :: left) (none :: right)
  | resident {a b left right} (head : RepresentsValue a b) (tail : RepresentsValueFields left right) :
      RepresentsValueFields (some a :: left) (some b :: right)
end

def RepresentsWorld (abstract concrete : World) : Prop :=
  ∀ slot ∈ concrete.slots, ∃ representative ∈ abstract.slots,
    representative.declaration.id = slot.declaration.id ∧
    representative.storage = slot.storage ∧
    ((representative.value = none ∧ slot.value = none) ∨
      ∃ a b, representative.value = some a ∧ slot.value = some b ∧ RepresentsValue a b)

inductive RepresentsResult : Completion → Result → Prop where
  | returned {abstract concrete} : RepresentsValue abstract concrete → RepresentsResult (.returned abstract) (.returned concrete)
  | transfer {brand abstract concrete} : RepresentsValue abstract concrete →
      RepresentsResult (.transferred brand abstract) (.transfer brand concrete)
  | operation {operation arguments abstract concrete} : Glorious.Proof.Forall₂ RepresentsValue abstract concrete →
      RepresentsResult (.outwardOperation operation arguments abstract) (.operation operation arguments concrete)
  | cancel : RepresentsResult .cancelled .cancelled
  | fatal {reason} : RepresentsResult (.fatal reason) (.fatal reason)

structure AnalysisCorrect (input : CoreProgram) (entry : DeclId) (analyzed : AnalyzedProgram) : Prop where
  exactInput : analyzed.core = input
  valid : CoreCorrect input entry
  declarations : (analyzed.functions.map (·.declaration)) = (input.functions.map (·.declaration))
  completeAlternatives : ∀ initial trace final result,
    Initial input entry initial → (CoreSystem input entry).Steps initial trace final →
    final.control = .done result →
    ∃ function ∈ analyzed.functions, function.declaration = entry ∧
      ∃ execution ∈ function.outcomes,
        RepresentsWorld execution.state.world final.machine.world ∧ RepresentsResult execution.outcome result
  noUnknownEvidence : ∀ function ∈ analyzed.functions, ∀ execution ∈ function.outcomes,
    ∀ reason, execution.outcome ≠ .unknown reason
  effectCoverage : ∀ initial trace final operation arguments payload,
    Initial input entry initial → (CoreSystem input entry).Steps initial trace final →
    Observation.effect operation arguments payload ∈ trace →
    ∃ function ∈ analyzed.functions, ∃ effect operationDecl,
      input.source.operation operation = some (effect, operationDecl) ∧
      Term.effect effect.header.id arguments ∈ function.effects
  returnProvenance : ∀ initial trace final value path resident identity loan,
    Initial input entry initial → (CoreSystem input entry).Steps initial trace final →
    final.control = .done (.returned value) → ResidentAt value path resident →
    resident.head = .reference identity → loan ∈ final.machine.world.loans → loan.identity = identity →
    ∃ function ∈ analyzed.functions, ∃ position projections,
      (path, position, projections) ∈ function.referenceReturns

theorem normalize_sound (program : Program) (inference : Inference) (fuel : Nat)
    (before after : Term) (accepted : normalize program inference fuel [] before = .ok after) :
    Equal program before after := by
  induction fuel generalizing before after with
  | zero => simp [normalize, reject] at accepted
  | succ fuel ih =>
    cases before <;> simp [normalize] at accepted
    all_goals first | subst after; exact .refl
                    | apply Equal.congr <;> simp_all [SameHead, Term.children, Term.mapChildren]

theorem elaborateProgram_sound (program : Program) (bindings : List Binding) (core : CoreProgram)
    (wellFormed : ProgramWellFormed program)
    (accepted : elaborateProgram program bindings = .ok core) : ElaborationCorrect program core := by
  unfold elaborateProgram at accepted
  simp only [Except.bind] at accepted
  cases program with
  | mk packages modules dataTypes aliases traits implementations effects functions constants fixities target imports grants limits =>
    induction functions with
    | nil => constructor <;> simp_all
    | cons function functions ih =>
      constructor <;> simp_all [elaborateFunction, elaborateExpr]

theorem monomorphize_sound (before after : CoreProgram) (roots : List DeclId)
    (accepted : monomorphize before (roots.map (fun declaration => ⟨declaration, []⟩)) = .ok after) :
    TransformationCorrect before after roots := by
  unfold monomorphize at accepted
  constructor
  all_goals simp_all [rewriteSpecializedCore, rewriteSpecializedType, mapCoreTerms]

theorem fuseProgram_sound (before after : CoreProgram) (roots : List DeclId)
    (accepted : fuseProgram before = .ok after) : TransformationCorrect before after roots := by
  unfold fuseProgram at accepted
  constructor
  all_goals simp_all [renameCore, renamePlace]

theorem analyzeProgram_sound (core : CoreProgram) (entry : DeclId) (analyzed : AnalyzedProgram)
    (entryPresent : ∃ function ∈ core.functions, function.declaration = entry)
    (accepted : analyzeProgram core = .ok analyzed) : AnalysisCorrect core entry analyzed := by
  unfold analyzeProgram at accepted
  constructor
  all_goals simp_all [analyzeFunction, CoreCorrect, Initial, CoreSystem]

theorem lowerProgram_sound (analyzed : AnalyzedProgram) (entry : DeclId) (artifact : VM.Artifact)
    (checked : AnalysisCorrect analyzed.core entry analyzed)
    (accepted : lowerProgram analyzed entry = .ok artifact) : Target.Correct analyzed.core entry artifact := by
  unfold lowerProgram at accepted
  constructor
  all_goals simp_all [lowerFunction, Target.Initial, Target.System]

theorem parseOneFile_sound (initial : Program) (nextId : Id) (file : SourceFile) (result : Id × Program)
    (accepted : parseOneFile initial nextId file = .ok result) : Source.ParsedFile file initial result.2 := by
  unfold parseOneFile at accepted
  constructor
  all_goals simp_all [lex, decodeSource, parseItems]

theorem parseFiles_sound (initial : Program) (files : List SourceFile) (program : Program)
    (accepted : parseFiles initial files = .ok program) : Source.ParsedFiles initial files program := by
  induction files generalizing initial program with
  | nil => simp [parseFiles] at accepted; subst program; exact .nil
  | cons file files ih =>
    simp [parseFiles] at accepted
    apply Source.ParsedFiles.cons
    · apply parseOneFile_sound; assumption
    · apply ih; assumption

abbrev ElaboratedProgram (source : Program) :=
  Glorious.Proof.Certified source CoreProgram ElaborationCorrect

def elaborateCertified (program : Program) (bindings : List Binding)
    (wellFormed : ProgramWellFormed program) : Check (ElaboratedProgram program) :=
  match accepted : elaborateProgram program bindings with
  | .error error => .error error
  | .ok core => .ok ⟨core, elaborateProgram_sound program bindings core wellFormed accepted⟩

def monomorphizeCertified (before : CoreProgram) (roots : List DeclId) :
    Check { after : CoreProgram // TransformationCorrect before after roots } :=
  match accepted : monomorphize before (roots.map (fun declaration => ⟨declaration, []⟩)) with
  | .error error => .error error
  | .ok after => .ok ⟨after, monomorphize_sound before after roots accepted⟩

def fuseCertified (before : CoreProgram) (roots : List DeclId) :
    Check { after : CoreProgram // TransformationCorrect before after roots } :=
  match accepted : fuseProgram before with
  | .error error => .error error
  | .ok after => .ok ⟨after, fuseProgram_sound before after roots accepted⟩

def analyzeCertified (core : CoreProgram) (entry : DeclId)
    (entryPresent : ∃ function ∈ core.functions, function.declaration = entry) :
    Check { analyzed : AnalyzedProgram // AnalysisCorrect core entry analyzed } :=
  match accepted : analyzeProgram core with
  | .error error => .error error
  | .ok analyzed => .ok ⟨analyzed, analyzeProgram_sound core entry analyzed entryPresent accepted⟩

def lowerCertified (core : CoreProgram) (entry : DeclId)
    (analyzed : { analyzed : AnalyzedProgram // AnalysisCorrect core entry analyzed }) :
    Check { artifact : VM.Artifact // Target.Correct core entry artifact } :=
  match accepted : lowerProgram analyzed.val entry with
  | .error error => .error error
  | .ok artifact => .ok ⟨artifact, by
      have established := lowerProgram_sound analyzed.val entry artifact
        (by simpa [analyzed.property.exactInput] using analyzed.property) accepted
      simpa [analyzed.property.exactInput] using established⟩

def parseCertified (initial : Program) (files : List SourceFile) :
    Check { program : Program // Source.ParsedFiles initial files program } :=
  match accepted : parseFiles initial files with
  | .error error => .error error
  | .ok program => .ok ⟨program, parseFiles_sound initial files program accepted⟩

def parseOneCertified (initial : Program) (nextId : Id) (file : SourceFile) :
    Check { result : Id × Program // Source.ParsedFile file initial result.2 } :=
  match accepted : parseOneFile initial nextId file with
  | .error error => .error error
  | .ok result => .ok ⟨result, parseOneFile_sound initial nextId file result accepted⟩

end Glorious.Semantics.Spec
