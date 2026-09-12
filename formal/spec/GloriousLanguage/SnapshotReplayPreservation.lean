import GloriousLanguage.SnapshotResourcePreservation
import GloriousLanguage.SnapshotWorldTyping

/-! The actual copied root product retains replay and cancellation admission.
Resource closure comes from the mixed graph proof; quantity transport uses
the same finite runtime-region permutation as world typing. -/
namespace Glorious.Language.Execution

theorem CopiesSnapshot.resident_principal {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {address : Address} {value : Value} {principal : Principal}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    (resident : before.world.Resident address value) (capability : PrincipalOf program.declarations value.type principal) :
    PrincipalOf program.declarations (map.value value).type principal := by
  rw [map.value_type,copied.relocation.term_permutation typed.1 (typed.resident_runtimeRegionsBelow valid inventory resident)]
  exact capability.permute valid (copied.relocation.permutation typed.1)

theorem Relocation.value_shellLive (map : Relocation) (value : Value) :
    (map.value value).shellLive = value.shellLive := by cases value; rfl

theorem Relocation.value_not_label {map : Relocation} {value : Value}
    (unlabeled : ∀ brand, value.head ≠ .label brand) : ∀ brand, (map.value value).head ≠ .label brand := by
  intro brand head
  cases value with
  | resident owner type original live fields resources =>
      cases original <;> simp [Relocation.value,Value.head] at head
      exact unlabeled _ rfl

theorem Relocation.value_not_available {map : Relocation} {value : Value}
    (unavailable : ∀ identity, value.head ≠ .available identity) :
    ∀ identity, (map.value value).head ≠ .available identity := by
  intro identity head
  cases value with
  | resident owner type original live fields resources =>
      cases original <;> simp [Relocation.value,Value.head] at head
      exact unavailable _ rfl

theorem CopiesSnapshot.replayable_copied {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after) :
    Replayable program after.world (map.roots.map map.root) := by
  refine ⟨copied.suspensible typed.1,?_,?_,?_⟩
  · intro address value included resident
    rw [copied.result] at resident
    obtain ⟨original,source,captured,located,_,rfl⟩ := copied.relocation.captured_origin typed.1 included resident
    obtain ⟨principal,unlabeled,unavailable,readOnly⟩ :=
      copied.replayable.2.1 original source (copied.relocation.roots ▸ captured) located
    refine ⟨fun live => copied.resident_principal valid inventory typed located (principal ((map.value_shellLive source) ▸ live)),
      Relocation.value_not_label unlabeled,Relocation.value_not_available unavailable,?_⟩
    intro binding member
    rw [map.value_resources] at member
    obtain ⟨original,sourceMember,rfl⟩ := List.mem_map.mp member
    exact Relocation.binding_readOnly (readOnly original sourceMember)
  · intro address value identity loan included resident head found
    rw [copied.result] at resident found
    obtain ⟨original,source,captured,located,_,rfl⟩ := copied.relocation.captured_origin typed.1 included resident
    obtain ⟨previous,reference,rfl⟩ := Relocation.reference_origin head
    obtain ⟨originalLoan,selected,live⟩ := typed.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 original source previous located reference
    have shared := copied.storageReady.references original source previous originalLoan captured located reference selected
    have includedLoan := copied.relocation.reference_loan captured located reference selected live shared
    have equal := Option.some.inj ((copied.relocation.copied_loan (homes := suspension.homes) typed.1 selected includedLoan).symm.trans found)
    subst loan
    exact shared
  · intro identity loan found live included
    rw [copied.result] at found
    obtain ⟨previous,original,present,selected,_,rfl⟩ := copied.relocation.captured_loan_origin typed.1 found live included
    exact (copied.relocation.selected_loan selected present).2

theorem Relocation.dropHook_original {program : Program} {map : Relocation} {type : Term} {hook : DeclId}
    (selected : DropHook program (map.term type) (some hook)) : DropHook program type (some hook) := by
  rcases selected with ⟨identity,arguments,data,same,found,hookEq⟩ | ⟨_,impossible⟩
  · cases type <;> simp [Relocation.term,Term.renameRuntimeRegions] at same
    obtain ⟨rfl,_⟩ := same
    exact Or.inl ⟨_,_,data,rfl,found,hookEq⟩
  · contradiction

theorem CopiesSnapshot.mayDispose {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {address : Address} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    (resident : before.world.Resident address value) (disposable : MayDispose program.declarations value) :
    MayDispose program.declarations (map.value value) := by
  intro path current located
  obtain ⟨original,inside,rfl⟩ := Relocation.residentAt_origin located
  obtain ⟨discard,hook⟩ := disposable path original inside
  constructor
  · intro live
    obtain ⟨principal,capability,quantity⟩ := discard ((map.value_shellLive original) ▸ live)
    exact ⟨principal,copied.resident_principal valid inventory typed (resident.nested inside) capability,quantity⟩
  · intro identity selected
    rw [map.value_type] at selected
    exact Relocation.value_initialized (hook identity (Relocation.dropHook_original selected))

theorem CopiesSnapshot.cancelable {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    (admitted : Cancelable program before.world suspension.roots) :
    Cancelable program after.world (map.roots.map map.root) := by
  refine ⟨copied.suspensible typed.1,?_⟩
  intro address value included resident
  rw [copied.result] at resident
  obtain ⟨original,source,captured,located,_,rfl⟩ := copied.relocation.captured_origin typed.1 included resident
  exact copied.mayDispose valid inventory typed located
    (admitted.2 original source (copied.relocation.roots ▸ captured) located)

end Glorious.Language.Execution
