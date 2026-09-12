import GloriousLanguage.CopyStructure
import GloriousLanguage.ReferenceTransferPreservation
import GloriousLanguage.CapabilityInversion

/-! Copy transports the same actual reference/resource graph as move. Only
structural residents are copied: once an explicit reference/resource edge is
followed, its stored target is unchanged. Declared Copy stability and actual
read-only bindings discharge the closed-invariant boundary. -/
namespace Glorious.Language

/-- Proof-only classification of a reached result node: either an actual
structural subtree Copy, or the unchanged target of a world edge. -/
def CopyTree.Origin (program : Program) (map : Identity → Identity) (original resident : Value) : Prop :=
  resident = original ∨ ∃ first last raw names,
    CopyTree program first original last raw names ∧ resident = raw.mapBindingOrigins map

theorem CopyTree.Origin.resources_eq {program : Program} {map : Identity → Identity}
    {original resident : Value} (origin : CopyTree.Origin program map original resident) :
    resident.resources = original.resources := by
  rcases origin with rfl | ⟨first,last,raw,names,copied,rfl⟩
  · rfl
  · exact copied.resources_eq map

theorem CopyTree.Origin.reference_iff {program : Program} {map : Identity → Identity}
    {original resident : Value} (origin : CopyTree.Origin program map original resident) (identity : Identity) :
    resident.head = .reference identity ↔ original.head = .reference identity := by
  rcases origin with rfl | ⟨first,last,raw,names,copied,rfl⟩
  · rfl
  · exact copied.reference_iff map identity

/-- Pullback through the one resident graph retains the exact authority and
access path. Pointer bits never participate in the induction. -/
theorem CopyTree.reachable_origin {program : Program} {next finish : Nat} {value copied resident : Value}
    {names : Table Identity} (copy : CopyTree program next value finish copied names) (map : Identity → Identity)
    {world : World} {authority current : Authority} {incoming access : Access}
    (reached : (copied.mapBindingOrigins map).ReachableResident world authority incoming resident current access) :
    ∃ original, value.ReachableResident world authority incoming original current access ∧
      CopyTree.Origin program map original resident := by
  induction reached with
  | resident located =>
      obtain ⟨raw,inside,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp located
      obtain ⟨original,first,last,names,inside,copied⟩ := copy.resident_copy _ _ inside
      exact ⟨original,.resident inside,Or.inr ⟨first,last,raw,names,copied,rfl⟩⟩
  | referent _ reference found stored located ih =>
      obtain ⟨original,prior,origin⟩ := ih
      exact ⟨_,.referent prior ((origin.reference_iff _).mp reference) found stored located,Or.inl rfl⟩
  | resource _ member stored located ih =>
      obtain ⟨original,prior,origin⟩ := ih
      exact ⟨_,.resource prior (origin.resources_eq ▸ member) stored located,Or.inl rfl⟩

theorem StorageBinding.HeldBy.readOnly_owner {world : World} {binding : StorageBinding} {owner : Identity}
    (held : binding.HeldBy world owner) (shared : binding.ReadOnly) (recipient : Identity) :
    binding.HeldBy world recipient := by
  refine ⟨?_,held.2⟩
  obtain ⟨backing,same⟩ := shared
  simpa only [same,Authority.Custodied] using held.1

theorem Value.InvariantClosed.copyTree {program : RuntimeProgram} {world : World}
    {next finish : Nat} {value copied : Value} {names : Table Identity}
    (ready : value.InvariantClosed program world) (copy : CopyTree program.declarations next value finish copied names)
    (map : Identity → Identity) : (copied.mapBindingOrigins map).InvariantClosed program world := by
  have same := (Value.mapBindingOrigins_type copied map).trans copy.type_eq
  unfold Value.InvariantClosed at ready ⊢
  rw [same]
  cases type : value.type with
  | nominal identity arguments =>
    simp only [type] at ready ⊢
    obtain ⟨data,found,closed⟩ := ready
    refine ⟨data,found,?_⟩
    cases declared : data.invariant with
    | none => simpa only [declared,copy.resources_eq map] using closed
    | some invariant =>
        simp only [declared] at closed ⊢
        obtain ⟨contract,selected,owner,holds⟩ := closed
        exact ⟨contract,selected,owner,contract.copied world next value finish copied names map copy holds⟩
  | _ => simpa only [type,copy.resources_eq map] using ready

theorem Value.ResourcesClosed.copyTree {program : RuntimeProgram} {world : World}
    {next finish : Nat} {value copied : Value} {names : Table Identity}
    (ready : value.ResourcesClosed program world) (copy : CopyTree program.declarations next value finish copied names)
    (map : Identity → Identity) : (copied.mapBindingOrigins map).ResourcesClosed program world := by
  intro resident authority access reached
  obtain ⟨original,prior,origin⟩ := copy.reachable_origin map reached
  have closed := ready original authority access prior
  rcases origin with rfl | ⟨first,last,raw,names,subtree,rfl⟩
  · exact closed
  · refine ⟨?_,closed.2.copyTree subtree map⟩
    intro binding member
    have originalMember : binding ∈ original.resources := subtree.resources_eq map ▸ member
    exact (closed.1 binding originalMember).readOnly_owner (subtree.resources_readOnly binding originalMember) _

theorem Value.LoansRestored.copyTree {program : RuntimeProgram} {world : World}
    {next finish : Nat} {value copied : Value} {names : Table Identity}
    (ready : value.LoansRestored program world) (copy : CopyTree program.declarations next value finish copied names)
    (map : Identity → Identity) : (copied.mapBindingOrigins map).LoansRestored program world := by
  intro identity authority access reached
  obtain ⟨resident,reached,reference⟩ := reached
  obtain ⟨original,prior,origin⟩ := copy.reachable_origin map reached
  exact ready identity authority access ⟨original,prior,(origin.reference_iff identity).mp reference⟩

theorem Value.ReferencesAccessible.copyTree {program : Program} {world : World}
    {next finish : Nat} {value copied : Value} {names : Table Identity} {authority : Authority} {access : Access}
    (ready : value.ReferencesAccessible world authority access) (copy : CopyTree program next value finish copied names)
    (map : Identity → Identity) : (copied.mapBindingOrigins map).ReferencesAccessible world authority access := by
  intro identity current incoming reached
  obtain ⟨resident,reached,reference⟩ := reached
  obtain ⟨original,prior,origin⟩ := copy.reachable_origin map reached
  exact ready identity current incoming ⟨original,prior,(origin.reference_iff identity).mp reference⟩

theorem Value.ResourcesAccessible.copyTree {program : RuntimeProgram} {world : World}
    {next finish : Nat} {value copied : Value} {names : Table Identity} {access : Access}
    (ready : value.ResourcesAccessible program world access) (copy : CopyTree program.declarations next value finish copied names)
    (map : Identity → Identity) : (copied.mapBindingOrigins map).ResourcesAccessible program world access := by
  refine ⟨ready.1.copyTree copy map,ready.2.1.copyTree copy map,ready.references.copyTree copy map,?_⟩
  intro resident authority incoming reached binding member
  obtain ⟨original,prior,origin⟩ := copy.reachable_origin map reached
  exact ready.2.2.2 original authority incoming prior binding (origin.resources_eq ▸ member)

theorem CopyTree.support_origin {program : Program} {world : World} {next finish : Nat}
    {value copied : Value} {names : Table Identity} (copy : CopyTree program next value finish copied names)
    (map : Identity → Identity) {address : Address} (supported : (copied.mapBindingOrigins map).Support world address) :
    value.Support world address := by
  obtain ⟨resident,authority,access,reached,edge⟩ := supported
  obtain ⟨original,prior,origin⟩ := copy.reachable_origin map reached
  refine ⟨original,authority,access,prior,?_⟩
  rcases edge with ⟨identity,loan,reference,found,rfl⟩ | ⟨binding,member,rfl⟩
  · exact Or.inl ⟨identity,loan,(origin.reference_iff identity).mp reference,found,rfl⟩
  · exact Or.inr ⟨binding,origin.resources_eq ▸ member,rfl⟩

theorem Value.HandoffReady.copy {program : RuntimeProgram} {world : World} {next finish : Nat}
    {value copied : Value} {access : Access} {footprint : List Address}
    (ready : value.HandoffReady program world access footprint)
    (copy : CopyValue program.declarations next value finish copied) :
    copied.HandoffReady program world access footprint := by
  cases copy with
  | copy tree _ =>
      refine ⟨ready.1.copyTree tree _,?_⟩
      intro mutation member address supported
      exact ready.2 mutation member address (tree.support_origin _ supported)

/-- The boundary property is about actual first edges of the copied resident
tree. After such a shared edge, the common graph already retains shared access
to every reached target, even when that target contains a unique reference. -/
def Value.SharedEdges (world : World) (value : Value) : Prop :=
  ∀ path resident, ResidentAt value path resident →
    (∀ identity loan, resident.head = .reference identity → world.loans.get identity = some loan → loan.mode = .shared) ∧
    ∀ binding ∈ resident.resources, binding.ReadOnly

theorem CopyTree.reference_shared {program : Kernel.Program} {world : World} {next finish : Nat}
    {value copied : Value} {names : Table Identity} {identity : Identity} {loan : Loan}
    (valid : ProgramWellFormed program.declarations) (copy : CopyTree program.declarations next value finish copied names)
    (typed : Typing.ValueTyped program world value) (reference : value.head = .reference identity)
    (found : world.loans.get identity = some loan) : loan.mode = .shared := by
  have capability : PrincipalOf program.declarations value.type .duplicable := by cases copy; assumption
  cases typed <;> try { simp [Value.head] at reference }
  case aggregate shape _ =>
    rcases shape with ⟨_,_,head⟩ | ⟨_,_,_,_,_,_,head,_⟩ | ⟨_,_,_,_,_,_,_,head,_⟩ <;>
      rw [head] at reference <;> cases reference
  case reference selected active mode region located =>
    cases reference
    have same := Option.some.inj (found.symm.trans selected)
    cases same
    exact mode.trans (PrincipalOf.reference_copy_shared valid capability)

theorem CopyTree.sharedEdges {program : Kernel.Program} {world : World} {next finish : Nat}
    {value copied : Value} {names : Table Identity}
    (valid : ProgramWellFormed program.declarations) (copy : CopyTree program.declarations next value finish copied names)
    (typed : Typing.ValueTyped program world value) (map : Identity → Identity) :
    (copied.mapBindingOrigins map).SharedEdges world := by
  intro path resident located
  obtain ⟨raw,inside,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp located
  obtain ⟨original,first,last,names,inside,subtree⟩ := copy.resident_copy _ _ inside
  refine ⟨?_,?_⟩
  · intro identity loan reference found
    exact subtree.reference_shared valid (typed.resident inside) ((subtree.reference_iff map identity).mp reference) found
  · intro binding member
    exact subtree.resources_readOnly binding (subtree.resources_eq map ▸ member)

theorem CopyValue.sharedEdges {program : Kernel.Program} {world : World} {next finish : Nat} {value copied : Value}
    (valid : ProgramWellFormed program.declarations) (copy : CopyValue program.declarations next value finish copied)
    (typed : Typing.ValueTyped program world value) : copied.SharedEdges world := by
  cases copy with
  | copy tree _ => exact tree.sharedEdges valid typed _

theorem Value.ReachableResident.sharedRoot {world : World} {value resident : Value}
    {authority : Authority} {access : Access} (shared : value.SharedEdges world)
    (reached : value.ReachableResident world .owner .owned resident authority access) :
    (∃ path, ResidentAt value path resident ∧ authority = .owner ∧ access = .owned) ∨
      value.ReachableResident world .owner .shared resident authority access := by
  induction reached with
  | resident located => exact Or.inl ⟨_,located,rfl,rfl⟩
  | referent _ reference found stored located ih =>
      rcases ih with ⟨path,inside,rfl,rfl⟩ | prior
      · have mode := (shared path _ inside).1 _ _ reference found
        have prior := Value.ReachableResident.referent (authority := .owner) (incoming := .shared)
          (.resident inside) reference found stored located
        exact Or.inr (by simpa [ReferenceAccess,mode] using prior)
      · exact Or.inr (.referent prior reference found stored located)
  | resource _ member stored located ih =>
      rcases ih with ⟨path,inside,rfl,rfl⟩ | prior
      · obtain ⟨backing,readOnly⟩ := (shared path _ inside).2 _ member
        have prior := Value.ReachableResident.resource (authority := .owner) (incoming := .shared)
          (.resident inside) member stored located
        exact Or.inr (by simpa [Authority.resourceView,ResourceAccess,readOnly] using prior)
      · exact Or.inr (.resource prior member stored located)

/-- Owning the fresh copied carrier does not strengthen any reachable edge.
This follows from the actual typed Copy traversal and the canonical capability
producer, rather than an added exclusive-permission premise on Copy. -/
theorem Value.ResourcesAccessible.owned_of_shared {program : RuntimeProgram} {world : World} {value : Value}
    (ready : value.ResourcesAccessible program world .shared) (shared : value.SharedEdges world) :
    value.ResourcesAccessible program world .owned := by
  refine ⟨ready.1,ready.2.1,?_,?_⟩
  · intro identity authority access reached
    obtain ⟨resident,reached,reference⟩ := reached
    rcases reached.sharedRoot shared with ⟨path,inside,rfl,rfl⟩ | prior
    · obtain ⟨loan,found,live,permitted⟩ := ready.references identity .owner .shared ⟨resident,.resident inside,reference⟩
      have mode := (shared path resident inside).1 identity loan reference found
      exact ⟨loan,found,live,by simpa [ReferenceAccess,mode] using permitted⟩
    · exact ready.references identity authority access ⟨resident,prior,reference⟩
  · intro resident authority access reached binding member
    rcases reached.sharedRoot shared with ⟨path,inside,rfl,rfl⟩ | prior
    · obtain ⟨backing,readOnly⟩ := (shared path resident inside).2 binding member
      have permitted := ready.2.2.2 resident .owner .shared (.resident inside) binding member
      simpa [Authority.resourceView,ResourceAccess,readOnly] using permitted
    · exact ready.2.2.2 resident authority access prior binding member

theorem Value.HandoffReady.copy_owned {program : Kernel.Program} {world : World} {next finish : Nat}
    {value copied : Value} {footprint : List Address} (valid : ProgramWellFormed program.declarations)
    (ready : value.HandoffReady program world .shared footprint) (typed : Typing.ValueTyped program world value)
    (copy : CopyValue program.declarations next value finish copied) :
    copied.HandoffReady program world .owned footprint := by
  have copiedReady := ready.copy copy
  exact ⟨copiedReady.1.owned_of_shared (copy.sharedEdges valid typed),copiedReady.2⟩

/-- The real installation frames every support of the copied graph. This
requires neither a typed nor a resource-closed post-state, and no allocation
ownership can be manufactured by copying a shared erased binding. -/
theorem Copies.handed_off_shared_ready {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address}
    (copied : Copies program before authority source destination after) :
    ∃ value, after.Stores destination value ∧ value.Initialized ∧ value.ResourcesAccessible program after .shared := by
  cases copied with
  | copy stored initialized ready permission vacant located copy written =>
      rename_i original cloned next installed
      have clonedReady := ready.copy copy
      have locations := World.write_locations written
      have rest := World.write_rest written
      have loans := congrArg World.loans rest
      change installed.loans = before.loans at loans
      have framed : cloned.SupportFramed before { installed with nextOwner := next } := by
        intro address supported
        refine ⟨?_,locations address.root⟩
        change installed.read address = before.read address
        exact World.write_disjoint written (clonedReady.2 destination (by simp) address supported)
      have preserved := clonedReady.1.frame (after := { installed with nextOwner := next })
        (.of_locations locations) loans framed
      refine ⟨cloned,?_,copy.initialized,preserved⟩
      have installedValue := World.write_read_inside written []
      simp only [List.append_nil] at installedValue
      change installed.Stores destination cloned at installedValue
      exact installedValue

/-- The complete ordinary Copy handoff: the actual newly owned carrier is
initialized and ready under its owned view, while every copied storage edge
remains shared. All permission evidence comes from the original typed value. -/
theorem Copies.handed_off_ready {program : Kernel.Program} {before after : World}
    {authority : Authority} {source destination : Address}
    (valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program before)
    (copied : Copies program before authority source destination after) :
    ∃ value, after.Stores destination value ∧ value.Initialized ∧ value.ResourcesAccessible program after .owned := by
  cases copied with
  | copy stored initialized ready permission vacant located copy written =>
      rename_i original cloned next installed
      have checked := typed.2.1 source original (World.resident_iff_stores.mpr stored)
      have clonedReady := ready.copy_owned valid checked copy
      have locations := World.write_locations written
      have rest := World.write_rest written
      have loans := congrArg World.loans rest
      change installed.loans = before.loans at loans
      have framed : cloned.SupportFramed before { installed with nextOwner := next } := by
        intro address supported
        refine ⟨?_,locations address.root⟩
        change installed.read address = before.read address
        exact World.write_disjoint written (clonedReady.2 destination (by simp) address supported)
      have preserved := clonedReady.1.frame (after := { installed with nextOwner := next })
        (.of_locations locations) loans framed
      refine ⟨cloned,?_,copy.initialized,preserved⟩
      have installedValue := World.write_read_inside written []
      simp only [List.append_nil] at installedValue
      change installed.Stores destination cloned at installedValue
      exact installedValue

end Glorious.Language
