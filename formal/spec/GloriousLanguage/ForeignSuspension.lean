import GloriousLanguage.ForeignAuthority

/-! Host mutations preserve the storage ownership of active suspensions.
The actual CanEndStorage guard prevents retirement while a suspension owns a
root; ordinary captured residents may still be lawfully mutated. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem World.write_availability {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : after.availability = before.availability := by
  have same := congrArg World.availability (World.write_rest written)
  exact same

theorem Clears.availability {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : after.availability = before.availability := by
  induction cleared with
  | nil => rfl
  | cons written _ ih => exact ih.trans (World.write_availability written)

theorem Memory.AllocatesBuffer.availability {program : Program} {custody : ClaimCustody} {before after : World}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer} {place : ResolvedPlace}
    (allocated : AllocatesBuffer program custody before domain element count base pointer place after) :
    after.availability = before.availability := by
  cases allocated
  rfl

theorem Memory.InstallsResidents.availability {program : Program} {before after : World}
    {addresses : List Address} {residents : List (Option Value)}
    (installed : InstallsResidents program before addresses residents after) :
    after.availability = before.availability := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih
  | resident _ _ written _ ih => exact ih.trans (World.write_availability written)

theorem Copies.availability {program : RuntimeProgram} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : after.availability = before.availability := by
  cases copied with
  | copy =>
    rename_i value cloned next afterWorld stored initialized ready permission vacant typed copiedValue written
    have same := World.write_availability written
    exact same

theorem Acquires.availability {program : RuntimeProgram} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : after.availability = before.availability := by
  cases acquired with
  | explicitMove moved => exact moved.availability
  | copy copied => exact copied.availability
  | move _ _ _ moved => exact moved.availability

theorem FormsLoan.availability {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.availability = before.availability := by
  cases borrowed with
  | borrow =>
    rename_i value afterWorld parent stored typed initialized regionLive admitted accessible permitted vacant destTyped parentEq written
    have same := World.write_availability written
    exact same

theorem Memory.BulkMove.availability {program : RuntimeProgram} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : after.availability = before.availability := by
  obtain ⟨_,clearedWorld,_,_,_,_,_,_,clears,installs⟩ := moved
  exact (Memory.InstallsResidents.availability installs).trans (Clears.availability clears)

theorem Memory.ReleasesBuffer.availability {program : Program} {before after : World} {place : ResolvedPlace}
    {pointer : RawPointer} {domain : Identity}
    (released : ReleasesBuffer program before place pointer domain after) :
    after.availability = before.availability := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    have initial : unclaimed.availability = before.availability := by cases claims; rfl
    have middle : cleared.availability = unclaimed.availability := World.write_availability written
    have final : after.availability = cleared.availability := by cases retires; rw [ended.2]
    exact final.trans (middle.trans initial)

theorem Memory.ReallocatesBuffer.availability {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation allocation : ResolvedPlace} {old : RawPointer}
    {domain : Identity} {element : Term} {newCount base : Nat} {result : RawPointer}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result allocation after) :
    after.availability = before.availability := by
  cases reallocated with
  | grow =>
    rename_i oldCount allocated moved ready bulkMove allocatedRun released
    have initial : allocated.availability = before.availability :=
      Memory.AllocatesBuffer.availability allocatedRun
    have middle : moved.availability = allocated.availability := bulkMove.availability
    exact released.availability.trans (middle.trans initial)

theorem Memory.RawRead.availability {program : RuntimeProgram} {before after : World} {source : ResolvedPlace}
    {pointer : RawPointer} {type : Term} {copy : Bool} {destination : Address}
    (read : RawRead program before source pointer type copy destination after) :
    after.availability = before.availability := by
  cases read with
  | read =>
    rename_i points layout range action
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.availability
    · exact Transfers.availability moved

theorem Memory.RawWrite.availability {program : RuntimeProgram} {before after : World}
    {source destination : ResolvedPlace} {pointer : RawPointer} {type : Term}
    (written : RawWrite program before source destination pointer type after) :
    after.availability = before.availability := by
  cases written with
  | write =>
    rename_i stored typeEq points layoutOf range permitted moved
    exact Transfers.availability moved

/-- Retirement cannot revoke ownership that still belongs to a suspension.
Final replay and cancellation must use their explicit restoration producer. -/
theorem Retires.suspended_location {before after : World} {retiredId id suspension : Identity} {root : Root}
    (retired : Retires before retiredId after) (selected : before.roots.get id = some root)
    (home : root.home = .suspended suspension) :
    (after.roots.get id).map Root.location = some root.location := by
  have separate : id ≠ retiredId := by
    intro same
    subst retiredId
    cases retired with
    | vacant _ _ _ safe => exact (safe.2.2 root selected suspension).1 home
  simpa only [selected,Option.map_some] using congrArg (Option.map Root.location) (retired.roots_other separate)

/-- Location-preserving producers cannot introduce an unaccounted root. This
is the reverse lookup consequence of their existing location theorem. -/
theorem World.root_origin_of_locations {before after : World} {id : Identity} {root : Root}
    (locations : (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (selected : after.roots.get id = some root) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  apply Option.map_eq_some_iff.mp
  rw [← locations,selected]
  rfl

theorem Allocates.suspended_origin {program : Program} {before after : World}
    {home region type layout mutable address} {id suspension : Identity} {root : Root}
    (allocated : Allocates program before home region type layout mutable address after)
    (notSuspended : home ≠ .suspended suspension)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases allocated
  by_cases fresh : id = before.nextRoot
  · subst id
    simp only [Table.get_set,Option.some.injEq] at selected
    exact False.elim (notSuspended (by simpa only [← selected] using suspended))
  · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ fresh] using selected,rfl⟩

theorem Memory.AllocatesBuffer.suspended_origin {program : Program} {custody : ClaimCustody} {before after : World}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer} {place : ResolvedPlace}
    {id suspension : Identity} {root : Root}
    (allocated : AllocatesBuffer program custody before domain element count base pointer place after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases allocated
  by_cases fresh : id = before.nextRoot
  · subst id
    simp only [Table.get_set,Option.some.injEq] at selected
    simp only [← selected] at suspended
    cases suspended
  · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ fresh] using selected,rfl⟩

theorem Retires.suspended_origin {before after : World} {retiredId id suspension : Identity} {root : Root}
    (retired : Retires before retiredId after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases retired with
  | vacant found _ _ safe =>
    by_cases same : id = retiredId
    · subst id
      simp only [Table.get_set,Option.some.injEq] at selected
      exact False.elim ((safe.2.2 _ found suspension).1 (by simpa only [← selected] using suspended))
    · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ same] using selected,rfl⟩

/-- A release leaves the complete location of a suspended root untouched: the
claim release moves no root row, the slot write preserves every row's location,
the retirement cannot name a suspended root (the release's own endability guard
excludes exactly those homes) and the region end only trims `liveRegions`. This
is the fact the `releaseBuffer` arm of `Mutation.suspended_location` needs,
stated without naming the raw pointer (which a `Mutation` pattern cannot bind). -/
theorem Memory.ReleasesBuffer.location_of_suspended {program : Program} {before after : World}
    {place : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    {id suspension : Identity} {root : Root}
    (released : ReleasesBuffer program before place pointer domain after)
    (rowAt : before.roots.get id = some root) (home : root.home = .suspended suspension) :
    (after.roots.get id).map Root.location = some root.location := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    have rowUnclaimed : unclaimed.roots.get id = some root := by cases claims; exact rowAt
    obtain ⟨writtenRoot,writtenValue,writtenAt,clearedEq⟩ := World.write_value_update written
    have rowCleared : ∃ row,
        (unclaimed.roots.set place.address.root { writtenRoot with value := writtenValue }).get id = some row ∧
        row.home = .suspended suspension := by
      by_cases target : id = place.address.root
      · subst target
        refine ⟨{ writtenRoot with value := writtenValue },?_,?_⟩
        · rw [Table.get_set]
        · have sameRoot : writtenRoot = root := Option.some.inj (by rw [← writtenAt]; exact rowUnclaimed)
          subst sameRoot
          simpa only using home
      · refine ⟨root,?_,home⟩
        rw [Table.get_set_other _ _ _ _ target]
        exact rowUnclaimed
    obtain ⟨row,rowAtSet,rowHome⟩ := rowCleared
    have rowAtCleared : cleared.roots.get id = some row := by rw [clearedEq]; exact rowAtSet
    have kept := retires.suspended_location rowAtCleared rowHome
    have sameLocation : row.location = root.location := by
      have locations := World.write_locations written id
      rw [rowAtCleared,rowUnclaimed] at locations
      exact Option.some.inj locations
    have endStep : (after.roots.get id).map Root.location = (retired.roots.get id).map Root.location := by
      rw [ended.2]
    exact endStep.trans (by simpa only [sameLocation] using kept)

theorem Memory.ReleasesBuffer.suspended_origin {program : Program} {before after : World}
    {place : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    {id suspension : Identity} {root : Root}
    (released : ReleasesBuffer program before place pointer domain after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    rw [ended.2] at selected
    obtain ⟨current,found,location⟩ := retires.suspended_origin selected suspended
    obtain ⟨original,originalAt,originalLocation⟩ :=
      World.root_origin_of_locations (World.write_locations written id) found
    have claimStep : unclaimed.roots.get id = before.roots.get id := by cases claims; rfl
    exact ⟨original,claimStep.symm.trans originalAt,originalLocation.trans location⟩

theorem Memory.ReallocatesBuffer.suspended_origin {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation allocation : ResolvedPlace} {old : RawPointer}
    {domain : Identity} {element : Term} {newCount base : Nat} {result : RawPointer}
    {id suspension : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result allocation after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases reallocated with
  | grow =>
    rename_i oldCount allocated moved ready bulkMove allocatedRun released
    obtain ⟨current,found,location⟩ := released.suspended_origin selected suspended
    obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := bulkMove
    obtain ⟨fresh,freshAt,freshLocation⟩ :=
      World.root_origin_of_locations ((installed.locations id).trans (cleared.locations id)) found
    have freshHome : fresh.home = .suspended suspension := by
      have same := congrArg Root.home (freshLocation.trans location)
      simpa only [Root.location,suspended] using same
    obtain ⟨original,originalAt,originalLocation⟩ := allocatedRun.suspended_origin freshAt freshHome
    exact ⟨original,originalAt,originalLocation.trans (freshLocation.trans location)⟩

namespace Foreign

theorem NewValue.availability {program : RuntimeProgram} {before after : World} {destination : Address}
    {type : Term} {head : ValueHead} {sources : List ResolvedPlace}
    (constructed : NewValue program before destination type head sources after) :
    after.availability = before.availability := by
  cases constructed with
  | construct =>
    rename_i residents taken afterWorld vacant typed ready separate cleared written
    have same := (World.write_availability written).trans (Clears.availability cleared)
    exact same

theorem Mutation.availability {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction} (changed : Mutation program policy before action after) :
    after.availability = before.availability := by
  cases changed with
  | allocate _ _ allocated => cases allocated; rfl
  | scalar _ stored => exact NewValue.availability stored.2.2
  | unit _ stored => exact NewValue.availability stored.2
  | pointer _ _ _ _ stored => exact NewValue.availability stored.2
  | aggregate _ _ _ _ constructed => exact NewValue.availability constructed
  | acquire _ _ acquired => exact acquired.availability
  | borrow _ _ borrowed => exact borrowed.availability
  | allocateBuffer _ allocated => exact Memory.AllocatesBuffer.availability allocated
  | allocateExterior _ _ allocated => cases allocated; rfl
  | reallocateBuffer _ _ _ reallocated => exact reallocated.availability
  | releaseBuffer _ _ _ released => exact released.availability
  | rawRead _ _ _ read => exact read.availability
  | rawWrite _ _ _ written => exact written.availability
  | rawBorrow _ _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.availability
  | bulkMove _ _ moved => exact moved.availability
  | retire _ _ retired => cases retired; rfl
  | endLoan ended => cases ended; rfl

theorem Mutations.availability {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World}
    {produced : List ProducedResource} {actions : List MutationAction}
    (changed : Mutations program custody policy before produced actions after) :
    after.availability = before.availability := by
  induction changed with
  | refl => rfl
  | cons first _ ih => exact ih.trans first.availability

/-- Every host mutation preserves a suspended root's complete location,
without requiring its current value or incoming references to be private. -/
theorem Mutation.suspended_location {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction} {id suspension : Identity} {root : Root}
    (changed : Mutation program policy before action after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (home : root.home = .suspended suspension) :
    (after.roots.get id).map Root.location = some root.location := by
  have framed (locations : ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location) :
      (after.roots.get id).map Root.location = some root.location := by simpa only [selected,Option.map_some] using locations id
  have exactRoot (same : after.roots.get id = before.roots.get id) :
      (after.roots.get id).map Root.location = some root.location := by rw [same,selected]; rfl
  have internalHome : InternalHome root := by intro domain; simp [home]
  cases changed with
  | allocate _ _ allocated => exact exactRoot (allocated.roots_other bound)
  | scalar _ stored => exact framed stored.2.2.locations
  | unit _ stored => exact framed stored.2.locations
  | pointer _ _ _ _ stored => exact framed stored.2.locations
  | aggregate _ _ _ _ constructed => exact framed constructed.locations
  | acquire _ _ acquired =>
    cases acquired with
    | explicitMove moved => exact framed moved.locations
    | copy copied => exact framed copied.locations
    | move _ _ _ moved => exact framed moved.locations
  | borrow _ _ borrowed => exact framed borrowed.locations
  | allocateBuffer _ allocated => exact exactRoot (allocated.roots_other bound)
  | reallocateBuffer _ _ _ reallocated => exact exactRoot (reallocated.private_root bound selected internalHome)
  | releaseBuffer _ _ _ released =>
    exact released.location_of_suspended selected home
  | rawRead _ _ _ read =>
    cases read with
    | read _ _ _ action =>
      rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
      · exact framed copied.locations
      · exact framed moved.locations
  | rawWrite _ _ _ written => cases written with | write _ _ _ _ _ _ moved => exact framed moved.locations
  | rawBorrow _ _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact framed formed.locations
  | bulkMove _ _ moved =>
    obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
    exact framed (fun key => (installed.locations key).trans (cleared.locations key))
  | retire _ _ retired => exact retired.suspended_location selected home
  | allocateExterior _ _ allocated => exact exactRoot (allocated.roots_other bound)
  | endLoan ended => cases ended; exact exactRoot rfl

theorem Mutations.suspended_location {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World}
    {produced : List ProducedResource} {actions : List MutationAction}
    {id suspension : Identity} {root : Root}
    (changed : Mutations program custody policy before produced actions after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (home : root.home = .suspended suspension) :
    (after.roots.get id).map Root.location = some root.location := by
  induction changed generalizing root with
  | refl => rw [selected]; rfl
  | cons first _ ih =>
    obtain ⟨current,found,location⟩ := Option.map_eq_some_iff.mp (first.suspended_location bound selected home)
    have currentHome : current.home = .suspended suspension := by
      have same : current.home = root.home := by simpa only [Root.location] using congrArg Root.home location
      exact same.trans home
    exact (ih (Nat.lt_of_lt_of_le bound first.homeExtension.counter) found currentHome).trans (congrArg some location)

/-- A host's ordinary allocation policy cannot allocate into a suspension.
Every other mutation derives reverse ownership from its actual storage action. -/
theorem Mutation.suspended_origin {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction} {id suspension : Identity} {root : Root}
    (changed : Mutation program policy before action after)
    (noSuspendedHome : ∀ home region, policy.home home region → ∀ sid, home ≠ .suspended sid)
    (selected : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  have framed (locations : ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location) :=
    World.root_origin_of_locations (locations id) selected
  cases changed with
  | allocate admitted _ allocated => exact allocated.suspended_origin (noSuspendedHome _ _ admitted _) selected home
  | allocateExterior admitted _ allocated =>
    exact allocated.suspended_origin (noSuspendedHome _ _ admitted _) selected home
  | scalar _ stored => exact framed stored.2.2.locations
  | unit _ stored => exact framed stored.2.locations
  | pointer _ _ _ _ stored => exact framed stored.2.locations
  | aggregate _ _ _ _ constructed => exact framed constructed.locations
  | acquire _ _ acquired =>
    cases acquired with
    | explicitMove moved => exact framed moved.locations
    | copy copied => exact framed copied.locations
    | move _ _ _ moved => exact framed moved.locations
  | borrow _ _ borrowed => exact framed borrowed.locations
  | allocateBuffer _ allocated => exact allocated.suspended_origin selected home
  | reallocateBuffer _ _ _ reallocated => exact reallocated.suspended_origin selected home
  | releaseBuffer _ _ _ released => exact released.suspended_origin selected home
  | rawRead _ _ _ read =>
    cases read with
    | read _ _ _ action =>
      rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
      · exact framed copied.locations
      · exact framed moved.locations
  | rawWrite _ _ _ written => cases written with | write _ _ _ _ _ _ moved => exact framed moved.locations
  | rawBorrow _ _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact framed formed.locations
  | bulkMove _ _ moved =>
    obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
    exact framed (fun key => (installed.locations key).trans (cleared.locations key))
  | retire _ _ retired => exact retired.suspended_origin selected home
  | endLoan ended => cases ended; exact ⟨root,selected,rfl⟩

theorem Mutations.suspended_origin {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World}
    {produced : List ProducedResource} {actions : List MutationAction}
    {id suspension : Identity} {root : Root}
    (changed : Mutations program custody policy before produced actions after)
    (noSuspendedHome : ∀ emitted home region,
      (policy emitted).home home region → ∀ sid, home ≠ .suspended sid)
    (selected : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  induction changed generalizing root with
  | refl => exact ⟨root,selected,rfl⟩
  | cons first _ ih =>
    obtain ⟨current,currentAt,location⟩ := ih selected home
    have currentHome : current.home = .suspended suspension := by
      simpa only [Root.location,home] using congrArg Root.home location
    obtain ⟨original,originalAt,originalLocation⟩ :=
      first.suspended_origin (noSuspendedHome _) currentAt currentHome
    exact ⟨original,originalAt,originalLocation.trans location⟩

theorem Policy.no_suspended_home {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial : World} {session : ForeignSession} {home : Home} {region : Identity}
    (admitted : (Policy program model contract initial session).home home region) (sid : Identity) :
    home ≠ .suspended sid := by
  rcases admitted with ⟨rfl,_⟩ | ⟨_,_,_,rfl | rfl⟩ <;> simp

/-- The actual host law supplies mutations, and these producer theorems
derive the captured storage's continued liveness and suspension ownership. -/
theorem Model.Lawful.host_suspended_root {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {actions : List MutationAction} {action : HostAction}
    {id suspension : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (rootAt : before.roots.get id = some root) (home : root.home = .suspended suspension) (live : root.live = true) :
    before.nextRoot ≤ after.nextRoot ∧ after.availability = before.availability ∧
    ∃ current, after.roots.get id = some current ∧ current.location = root.location ∧
      current.home = .suspended suspension ∧ current.live = true := by
  have changed := (lawful.step _ _ _ _ _ _ _ _ _ selected well active step).1
  obtain ⟨current,found,location⟩ := Option.map_eq_some_iff.mp
    (changed.suspended_location (World.root_bound well rootAt) rootAt home)
  have sameHome : current.home = root.home := by simpa only [Root.location] using congrArg Root.home location
  have sameLive : current.live = root.live := by simpa only [Root.location] using congrArg Root.live location
  exact ⟨changed.homeExtension.counter,changed.availability,current,found,location,sameHome.trans home,sameLive.trans live⟩

/-- No post-step suspension root is accepted as a new inventory certificate:
the host law and its concrete mutation sequence produce its predecessor. -/
theorem Model.Lawful.host_suspended_origin {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {actions : List MutationAction} {action : HostAction}
    {id suspension : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (rootAt : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  have changed := (lawful.step _ _ _ _ _ _ _ _ _ selected well active step).1
  exact changed.suspended_origin (fun _ _ _ admitted sid => Policy.no_suspended_home admitted sid) rootAt home

end Foreign
end Glorious.Language
