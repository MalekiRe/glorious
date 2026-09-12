import GloriousLanguage.ABI
import GloriousLanguage.LayoutContext
import GloriousLanguage.LayoutExecution

/-! Loader acceptance carries the actual descriptor, concrete layout and
target bounds into execution. Compatibility derives layout/capability/drop
agreement from those facts, while concrete type identity remains explicit. -/
namespace Glorious.Language

theorem DropHook.functional {program : Program} {type : Term} {first second : Option DeclId}
    (left : DropHook program type first) (right : DropHook program type second) : first = second := by
  rcases left with ⟨id,args,data,rfl,found,hook⟩ | ⟨notNominal,rfl⟩
  · rcases right with ⟨otherId,otherArgs,otherData,same,otherFound,otherHook⟩ | ⟨notNominal,_⟩
    · obtain ⟨rfl,rfl⟩ := Term.nominal.inj same
      have sameData := Option.some.inj (found.symm.trans otherFound)
      subst otherData
      exact hook.symm.trans otherHook
    · exact False.elim (notNominal id args rfl)
  · rcases right with ⟨id,args,data,same,_,_⟩ | ⟨_,rfl⟩
    · exact False.elim (notNominal id args same)
    · rfl

private theorem List.nodup_map_member_unique {α β : Type} {map : α → β} {values : List α}
    (unique : (values.map map).Nodup) {left right : α} (first : left ∈ values) (second : right ∈ values)
    (same : map left = map right) : left = right := by
  induction values with
  | nil => cases first
  | cons value rest ih =>
    have nodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with rfl | firstTail
    · rcases List.mem_cons.mp second with rfl | secondTail
      · rfl
      · exact False.elim (nodup.1 (same ▸ List.mem_map.mpr ⟨_,secondTail,rfl⟩))
    · rcases List.mem_cons.mp second with rfl | secondTail
      · exact False.elim (nodup.1 (same ▸ List.mem_map.mpr ⟨_,firstTail,rfl⟩))
      · exact ih nodup.2 firstTail secondTail

namespace ABI

theorem ConcreteType.Valid.layout_valid {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    {concrete : ConcreteType} (admitted : concrete.Valid program) : concrete.layout.Valid :=
  admitted.layout.valid valid

theorem ConcreteType.Valid.contract_unique {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    {first second : ConcreteType} (left : first.Valid program) (right : second.Valid program)
    (same : first.type = second.type) :
    first.layout = second.layout ∧ first.principal = second.principal ∧ first.drop = second.drop := by
  have layout := left.layout.unique valid rfl (same ▸ right.layout)
  have principal := left.principal.functional (same ▸ right.principal)
  have drop := left.drop.functional (same ▸ right.drop)
  exact ⟨layout,principal,drop⟩

theorem Descriptor.Valid.concrete_unique {program : Kernel.Program} {descriptor : Descriptor}
    (valid : descriptor.Valid program) {left right : ConcreteType}
    (first : left ∈ descriptor.concrete) (second : right ∈ descriptor.concrete)
    (same : left.identity = right.identity) : left = right :=
  List.nodup_map_member_unique valid.identities first second same

/-- Once both descriptors are admitted for the same target, exact concrete
type agreement is the remaining linking obligation. Equal layout alone never
establishes it; layout, principal and destructor agreement are derived. -/
theorem Descriptor.Valid.compatible_iff_types {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {left right : Descriptor}
    (first : left.Valid program) (second : right.Valid program) :
    Compatible left right ↔
      ∀ a ∈ left.concrete, ∀ b ∈ right.concrete, a.identity = b.identity → a.type = b.type := by
  constructor
  · intro compatible a first b second same
    exact (compatible.2.2.2.2.2.2.2.2.2 a first b second same).1
  · intro types
    have leftTarget := first.targetContract
    have rightTarget := second.targetContract
    refine ⟨leftTarget.generation.trans rightTarget.generation.symm,
      leftTarget.target.trans rightTarget.target.symm,leftTarget.triple.trans rightTarget.triple.symm,
      leftTarget.pointerBits.trans rightTarget.pointerBits.symm,leftTarget.endian.trans rightTarget.endian.symm,
      leftTarget.layoutIdentity.trans rightTarget.layoutIdentity.symm,
      leftTarget.callableConvention.trans rightTarget.callableConvention.symm,
      leftTarget.effectConvention.trans rightTarget.effectConvention.symm,
      leftTarget.manifest.trans rightTarget.manifest.symm,?_⟩
    intro a member b other same
    have type := types a member b other same
    exact ⟨type,(first.concrete a member).contract_unique valid (second.concrete b other) type⟩

theorem AdmittedArtifact.unique {program : Kernel.Program} {loader : LoaderContract} {bytes : List Nat}
    {first second : Artifact} (left : AdmittedArtifact program loader bytes first)
    (right : AdmittedArtifact program loader bytes second) : first = second :=
  Except.ok.inj (left.decoded.symm.trans right.decoded)

theorem AdmittedArtifact.canonical {program : Kernel.Program} {loader : LoaderContract} {bytes : List Nat}
    {artifact : Artifact} (admitted : AdmittedArtifact program loader bytes artifact) :
    AdmittedArtifact program loader (loader.canonical artifact) artifact :=
  { admitted with decoded := loader.roundtrip artifact admitted.format }

theorem AdmittedArtifact.compatible_iff_types {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {leftLoader rightLoader : LoaderContract}
    {leftBytes rightBytes : List Nat} {left right : Artifact}
    (first : AdmittedArtifact program leftLoader leftBytes left)
    (second : AdmittedArtifact program rightLoader rightBytes right) :
    Compatible left.descriptor right.descriptor ↔
      ∀ a ∈ left.descriptor.concrete, ∀ b ∈ right.descriptor.concrete, a.identity = b.identity → a.type = b.type :=
  first.descriptor.compatible_iff_types valid second.descriptor

theorem AdmittedArtifact.target_mismatch_rejected {program : Kernel.Program} {loader : LoaderContract}
    {bytes : List Nat} {artifact : Artifact} (different : ¬ artifact.descriptor.Matches program) :
    ¬ AdmittedArtifact program loader bytes artifact :=
  fun admitted => different admitted.descriptor.targetContract

theorem AdmittedArtifact.layout_identity_rejected {program : Kernel.Program} {loader : LoaderContract}
    {bytes : List Nat} {artifact : Artifact}
    (different : artifact.descriptor.layoutIdentity ≠ program.declarations.input.target.layoutIdentity) :
    ¬ AdmittedArtifact program loader bytes artifact :=
  AdmittedArtifact.target_mismatch_rejected (fun matching => different matching.layoutIdentity)

theorem AdmittedArtifact.concrete_rejected {program : Kernel.Program} {loader : LoaderContract}
    {bytes : List Nat} {artifact : Artifact} {concrete : ConcreteType}
    (member : concrete ∈ artifact.descriptor.concrete) (invalid : ¬ concrete.Valid program) :
    ¬ AdmittedArtifact program loader bytes artifact :=
  fun admitted => invalid (admitted.descriptor.concrete concrete member)

theorem AdmittedArtifact.oversized_rejected {program : Kernel.Program} {loader : LoaderContract}
    {bytes : List Nat} {artifact : Artifact} {concrete : ConcreteType}
    (member : concrete ∈ artifact.descriptor.concrete)
    (large : program.declarations.input.target.maximumObjectBytes < concrete.layout.size) :
    ¬ AdmittedArtifact program loader bytes artifact :=
  AdmittedArtifact.concrete_rejected member (fun valid => Nat.not_le_of_gt large valid.sizeLimit)

theorem AdmittedArtifact.unrepresentable_rejected {program : Kernel.Program} {loader : LoaderContract}
    {bytes : List Nat} {artifact : Artifact} {concrete : ConcreteType}
    (member : concrete ∈ artifact.descriptor.concrete)
    (invalid : ¬ IntegerRange program.declarations.input.target false .pointer concrete.layout.size ∨
      ¬ IntegerRange program.declarations.input.target false .pointer concrete.layout.alignment) :
    ¬ AdmittedArtifact program loader bytes artifact := by
  apply AdmittedArtifact.concrete_rejected member
  intro valid
  rcases invalid with size | alignment
  · exact size valid.sizeRange
  · exact alignment valid.alignmentRange

theorem AdmittedArtifact.layout_mismatch_rejected {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {loader : LoaderContract} {bytes : List Nat}
    {artifact : Artifact} {concrete : ConcreteType} {layout : Layout}
    (member : concrete ∈ artifact.descriptor.concrete)
    (actual : LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ concrete.type layout)
    (different : concrete.layout ≠ layout) : ¬ AdmittedArtifact program loader bytes artifact :=
  AdmittedArtifact.concrete_rejected member (fun admitted => different (admitted.layout.unique valid rfl actual))

theorem AdmittedArtifact.encoding_layout_unique {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {loader : LoaderContract} {bytes : List Nat}
    {artifact : Artifact} {concrete : ConcreteType} {world : World} {runtime : Memory.RuntimeAddresses}
    {address : Address} {value : Value} {layout : Layout} {encoding : List (Option Nat)}
    (admitted : AdmittedArtifact program loader bytes artifact) (member : concrete ∈ artifact.descriptor.concrete)
    (type : value.type = concrete.type) (encoded : Memory.Encodes program.declarations world runtime address value layout encoding) :
    concrete.layout = layout :=
  (admitted.descriptor.concrete concrete member).layout.unique valid rfl (type ▸ encoded.layoutOf)

/-- An actually accepted concrete descriptor supplies all representation
premises to the sole executable layout-query rule, including usize bounds.
No layout-existence or representability assumption is added at execution. -/
theorem AdmittedArtifact.layout_safe_unique_progress {program : Kernel.Program} {host : Foreign.Model}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {loader : LoaderContract} {bytes : List Nat} {artifact : Artifact} {concrete : ConcreteType}
    (admitted : AdmittedArtifact program loader bytes artifact) (member : concrete ∈ artifact.descriptor.concrete)
    {before : Execution.State} (typed : Typing.WorldTyped program before.world)
    {context : Execution.Context} {destination : Address} {binding : RuntimeBinding} {next : Kernel.Code}
    (task : before.task = .primitive context destination binding [concrete.type] [] next)
    (identity : binding.primitive = some .layout)
    (destinationType : Execution.DestinationType before.world destination
      (.tuple [.scalar (.integer false .pointer),.scalar (.integer false .pointer)])) :
    ∃ after, Execution.Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      ∀ event other, Execution.Step program host before event other → event = none ∧ other = after := by
  have concrete := admitted.descriptor.concrete concrete member
  exact Execution.Step.layout_safe_unique_progress valid inventory typed task identity concrete.layout.runtime_context
    ⟨concrete.sizeRange,concrete.alignmentRange⟩ destinationType

end ABI

end Glorious.Language
