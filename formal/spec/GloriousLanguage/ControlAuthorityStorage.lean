import GloriousLanguage.ControlAuthority
import GloriousLanguage.ControlStorageOrigin

/-! Control authority provenance follows actual place views, invocation
loans and pattern plans. In particular, a dereference gets its authority
from the referenced table entry, not from an address-only hypothesis. -/
namespace Glorious.Language

theorem Typing.ValueTyped.reference_recorded {program : Kernel.Program} {world : World} {value : Value} {id : Identity}
    (typed : Typing.ValueTyped program world value) (reference : value.head = .reference id) :
    (Authority.loan id).Recorded world.loans := by
  cases typed <;> simp_all [Value.head]
  case reference found _ _ _ _ => exact ⟨_,found⟩
  case aggregate head _ => simp [Execution.ConstructorHead] at head

theorem Typing.WorldTyped.reference_recorded {program : Kernel.Program} {world : World}
    {address : Address} {value : Value} {id : Identity}
    (typed : Typing.WorldTyped program world) (stored : world.Stores address value)
    (reference : value.head = .reference id) : (Authority.loan id).Recorded world.loans :=
  (typed.2.1 address value (World.resident_iff_stores.mpr stored)).reference_recorded reference

theorem ReferenceView.recorded {world : World} {handle : Address} {authority : Authority}
    {id : Identity} {mode : Mutability} {permission : Authority} {access : Access} {loan : Loan}
    (well : world.WellFormed) (recorded : authority.Recorded world.loans)
    (view : ReferenceView world handle authority id mode permission access)
    (found : world.loans.get id = some loan) : permission.Recorded world.loans := by
  rcases view with ⟨_,rfl,_⟩ | ⟨_,_,rfl,_⟩ | ⟨_,_,rfl,_⟩ <;>
    exact recorded.referenceView well found _

namespace Kernel

theorem ResolvesProjections.recorded {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {projections : List Projection}
    (resolved : ResolvesProjections world environment base authority projections result permission)
    (well : world.WellFormed)
    (recorded : authority.Recorded world.loans) : permission.Recorded world.loans := by
  induction resolved with
  | nil => exact recorded
  | field _ _ _ ih | index _ _ _ _ _ _ _ ih => exact ih recorded
  | vacantField => exact recorded
  | dereference _ _ _ _ found _ view _ ih => exact ih (view.recorded well recorded found)

theorem ResolvesPlace.recorded {world : World} {environment : Environment}
    {place : Place} {address : Address} {authority : Authority}
    (resolved : ResolvesPlace world environment place address authority)
    (well : world.WellFormed)
    (recorded : ∀ binding ∈ environment, binding.authority.Recorded world.loans) : authority.Recorded world.loans := by
  cases resolved with
  | localSlot selected projections => exact projections.recorded well (recorded _ selected.1)

theorem LendsResident.authority_recorded {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (recorded : authority.Recorded before.loans) : permission.Recorded after.loans := by
  cases lent with
  | owned => exact recorded
  | lent _ _ _ _ formed =>
    obtain ⟨_,_,found⟩ := formed.created_handle
    exact ⟨_,found⟩

theorem LendsResident.lease_authority_recorded {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after) :
    AuthoritySupport.Recorded (lease.toList.map (fun lease => .loan lease.loan)) after.loans := by
  cases lent with
  | owned => simp
  | lent _ _ _ _ formed =>
    obtain ⟨_,_,found⟩ := formed.created_handle
    simp only [Option.toList_some,List.map_cons,List.map_nil,AuthoritySupport.recorded_cons,
      AuthoritySupport.recorded_nil,and_true]
    exact ⟨_,found⟩

theorem BindsInputAt.authority_recorded {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region input binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (recorded : input.authority.Recorded before.loans) : binding.authority.Recorded after.loans := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.authority_recorded recorded
  | owned => trivial
  | storage _ _ _ claimed =>
    cases claimed
    simp only [ClaimedAuthority]
    split <;> exact ⟨_,Table.get_set _ _ _⟩
  | allocation _ _ _ _ moved => exact moved.suspensionExtension.recorded _ recorded
  | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact ⟨_,Table.get_set _ _ _⟩
  | loan _ _ _ _ moved => exact moved.suspensionExtension.recorded _ recorded

theorem BindsInputsAttemptFor.authority_recorded {program : RuntimeProgram} {recipient : ClaimCustody}
    {footprint : List Address} {before after : World} {activation scope region inputs bindings}
    {outcome : PreparationOutcome}
    (bound : BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    (recorded : ∀ input ∈ inputs, input.authority.Recorded before.loans) :
    ∀ binding ∈ bindings, binding.authority.Recorded after.loans := by
  induction bound with
  | nil | exhausted => simp
  | cons _ first rest ih =>
    have firstRecorded := first.authority_recorded (recorded _ (List.mem_cons_self))
    have restRecorded := ih (fun input member => first.suspensionExtension.recorded _
      (recorded input (List.mem_cons_of_mem _ member)))
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact rest.suspensionExtension.recorded _ firstRecorded
    · exact restRecorded binding member

theorem BindsPattern.authority_recorded {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (recorded : authority.Recorded before.loans) : binding.authority.Recorded after.loans := by
  cases bound with
  | owned bound => exact bound.authority_recorded recorded
  | borrowed => trivial

end Kernel

namespace Execution

open _root_.Glorious.Language.Kernel

theorem Context.bind_authority_support {context : Context} {localSlot : Local} {address : Address}
    {authority : Authority} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded context.authoritySupport loans) (fresh : authority.Recorded loans) :
    AuthoritySupport.Recorded (context.bind localSlot address authority).authoritySupport loans := by
  simp only [Context.authoritySupport,AuthoritySupport.recorded_append,AuthoritySupport.recorded_map] at recorded ⊢
  refine ⟨?_,recorded.2⟩
  intro binding member
  simp only [Context.bind,List.mem_cons,List.mem_filter] at member
  rcases member with rfl | ⟨member,_⟩
  · exact fresh
  · exact recorded.1 binding member

theorem Context.resolves_recorded {context : Context} {world : World} {place : Place}
    {address : Address} {authority : Authority}
    (well : world.WellFormed)
    (recorded : AuthoritySupport.Recorded context.authoritySupport world.loans)
    (resolved : ResolvesPlace world context.environment place address authority) : authority.Recorded world.loans :=
  resolved.recorded well (AuthoritySupport.recorded_map.mp (AuthoritySupport.recorded_append.mp recorded).1)

theorem ResolvedOperands.authority_support {world : World} {environment : Environment}
    {places : List Place} {operands : List ResolvedPlace}
    (resolved : ResolvedOperands world environment places operands) :
    AuthoritySupport.Recorded (operands.map ResolvedPlace.authority) world.loans := by
  rw [AuthoritySupport.recorded_map]
  induction resolved with
  | nil => simp
  | cons first _ ih =>
    intro operand member
    rcases List.mem_cons.mp member with rfl | member
    · exact first.2.recorded
    · exact ih operand member

theorem ArgumentInputs.authority_support {world : World} {context : Context} {index : Nat}
    {formals : List Local} {places : List Place} {inputs : List InvocationInput}
    (well : world.WellFormed)
    (recorded : AuthoritySupport.Recorded context.authoritySupport world.loans)
    (prepared : ArgumentInputs world context index formals places inputs) :
    AuthoritySupport.Recorded (inputs.map InvocationInput.authority) world.loans := by
  induction prepared with
  | nil => simp
  | cons resolved _ _ ih =>
    simp only [List.map_cons,AuthoritySupport.recorded_cons]
    exact ⟨Context.resolves_recorded well recorded resolved,ih⟩

theorem _root_.Glorious.Language.Kernel.PatternPlan.authority_support {program : Language.Program} {world : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Pattern}
    {actions : PatternActions} (planned : PatternPlan program world address authority access pattern actions)
    (well : world.WellFormed)
    (recorded : authority.Recorded world.loans) :
    AuthoritySupport.Recorded ((ScheduledPattern actions).flatMap PatternAction.authoritySupport) world.loans := by
  refine PatternPlan.rec
    (motive_1 := fun _ authority _ _ actions _ => authority.Recorded world.loans →
      AuthoritySupport.Recorded ((ScheduledPattern actions).flatMap PatternAction.authoritySupport) world.loans)
    (motive_2 := fun _ authority _ _ _ actions _ => authority.Recorded world.loans →
      AuthoritySupport.Recorded ((ScheduledPattern actions).flatMap PatternAction.authoritySupport) world.loans)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned recorded
  all_goals intros
  all_goals simp_all only [ScheduledPattern,List.nil_append,List.append_nil,List.flatMap_nil,List.flatMap_cons,
    List.flatMap_append,PatternAction.authoritySupport,AuthoritySupport.recorded_append,
    AuthoritySupport.recorded_cons,AuthoritySupport.recorded_nil,true_and,and_true]
  case refine_8 =>
    split <;> simp_all only [List.flatMap_cons,List.flatMap_nil,PatternAction.authoritySupport,
      AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,AuthoritySupport.recorded_nil,and_true]
  case refine_9 =>
    rename_i found _ _ _ _ view _ ih recorded
    have nested := ih (view.recorded well (recorded.lend _) found)
    split <;> simp_all only [List.flatMap_cons,List.flatMap_nil,PatternAction.authoritySupport,
      AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,AuthoritySupport.recorded_nil,and_true]

theorem PreparesEntry.authority_inputs {program : Kernel.Program} {callee : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program callee function before source inputs after)
    (recorded : AuthoritySupport.Recorded source.authoritySupport before.loans) :
    ∀ input ∈ inputs, input.authority.Recorded after.loans := by
  cases prepared with
  | supplied => exact AuthoritySupport.recorded_map.mp recorded
  | resident _ _ lent captures consumed =>
    simp only [EntrySource.authoritySupport,AuthoritySupport.recorded_cons,AuthoritySupport.recorded_map] at recorded
    intro input member
    rcases List.mem_append.mp member with captured | argument
    · exact consumed.suspensionExtension.recorded _ (captures.2 input captured).2.recorded
    · exact (lent.suspensionExtension.trans consumed.suspensionExtension).recorded _ (recorded.2 input argument)
  | contextual _ _ _ _ receiver witness _ consumed finished =>
    simp only [EntrySource.authoritySupport,AuthoritySupport.recorded_cons,AuthoritySupport.recorded_map] at recorded
    exact fun input member =>
      (((receiver.suspensionExtension.trans witness.suspensionExtension).trans consumed.suspensionExtension).trans
        finished.suspensionExtension).recorded _ (recorded.2.2 input member)

theorem EnterWorld.context_authority_support {program : Kernel.Program} {before : State} {caller context : Context}
    {function : Function} {source : EntrySource} {after : World}
    (entered : EnterWorld program before caller function source context after)
    (recorded : AuthoritySupport.Recorded source.authoritySupport before.world.loans) :
    AuthoritySupport.Recorded context.authoritySupport after.loans := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,bound,selected,region,prepares,incoming,binds,finish,contextEq,unsafeOk⟩ := entered.prepared
  have inputsRecorded := prepares.authority_inputs (recorded.mono region.suspensionExtension.recorded)
  have bindingsRecorded := binds.authority_recorded inputsRecorded
  have finalRecorded : AuthoritySupport.Recorded (environment.map StorageBinding.authority) after.loans :=
    (AuthoritySupport.recorded_map.mpr bindingsRecorded).mono finish.suspensionExtension.recorded
  simp only [contextEq,Context.authoritySupport,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    AuthoritySupport.recorded_append]
  exact ⟨finalRecorded,finalRecorded⟩

@[simp] theorem CloseRegions.authority_support (regions : List Identity) (next : Task) :
    (CloseRegions regions next).authoritySupport = next.authoritySupport := by
  unfold CloseRegions
  induction regions.eraseDups with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem RetireAddresses.authority_support (addresses : List Address) (next : Task) :
    (addresses.foldr (fun address nextTask => .retire address.root nextTask) next).authoritySupport = next.authoritySupport := by
  induction addresses with
  | nil => rfl
  | cons _ _ ih => exact ih

end Execution
end Glorious.Language
