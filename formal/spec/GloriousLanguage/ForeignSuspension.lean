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

theorem Copies.availability {program : Program} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : after.availability = before.availability := by
  cases copied with
  | copy _ _ _ _ _ _ written => have same := World.write_availability written; exact same

theorem Acquires.availability {program : Program} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : after.availability = before.availability := by
  cases acquired with
  | explicitMove moved => exact moved.availability
  | copy copied => exact copied.availability
  | move _ _ _ moved => exact moved.availability

theorem FormsLoan.availability {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    after.availability = before.availability := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ written => have same := World.write_availability written; exact same

theorem Memory.BulkMove.availability {program : Program} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : after.availability = before.availability := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  have first := congrArg World.availability cleared.rest
  have last := congrArg World.availability installed.rest
  exact last.trans first

theorem Memory.ReleasesBuffer.availability {program : Program} {before after : World} {pointer domain}
    (released : ReleasesBuffer program before pointer domain after) : after.availability = before.availability := by
  cases released with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    rcases ended with ⟨_,_,_,rfl⟩
    cases retired
    have same := World.write_availability written
    exact same

theorem Memory.ReallocatesBuffer.availability {program : Program} {before after : World}
    {old domain element count base result}
    (reallocated : ReallocatesBuffer program before old domain element count base result after) :
    after.availability = before.availability := by
  obtain ⟨_,_,_,allocatedWorld,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  have initial : allocatedWorld.availability = before.availability := by cases allocated; rfl
  exact released.availability.trans (moved.availability.trans initial)

theorem Memory.RawRead.availability {program : Program} {before after : World} {pointer type copy destination}
    (read : RawRead program before pointer type copy destination after) : after.availability = before.availability := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.availability
    · exact moved.availability

theorem Memory.RawWrite.availability {program : Program} {before after : World} {authority source pointer type}
    (written : RawWrite program before authority source pointer type after) : after.availability = before.availability := by
  cases written with
  | write _ _ _ _ _ moved => exact moved.availability

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
    | vacant _ _ _ safe => exact safe.2.2 root selected suspension home
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

theorem Memory.AllocatesBuffer.suspended_origin {program : Program} {before after : World}
    {domain element count base pointer} {id suspension : Identity} {root : Root}
    (allocated : AllocatesBuffer program before domain element count base pointer after)
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
      exact False.elim (safe.2.2 _ found suspension (by simpa only [← selected] using suspended))
    · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ same] using selected,rfl⟩

theorem Memory.ReleasesBuffer.suspended_origin {program : Program} {before after : World}
    {pointer domain} {id suspension : Identity} {root : Root}
    (released : ReleasesBuffer program before pointer domain after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  cases released with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    rw [ended.2] at selected
    obtain ⟨current,found,location⟩ := retired.suspended_origin selected suspended
    obtain ⟨original,originalAt,originalLocation⟩ :=
      World.root_origin_of_locations (World.write_locations written id) found
    exact ⟨original,originalAt,originalLocation.trans location⟩

theorem Memory.ReallocatesBuffer.suspended_origin {program : Program} {before after : World}
    {old domain element count base result} {id suspension : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program before old domain element count base result after)
    (selected : after.roots.get id = some root) (suspended : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  obtain ⟨current,found,location⟩ := released.suspended_origin selected suspended
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  obtain ⟨fresh,freshAt,freshLocation⟩ :=
    World.root_origin_of_locations ((installed.locations id).trans (cleared.locations id)) found
  have freshHome : fresh.home = .suspended suspension := by
    have same := congrArg Root.home (freshLocation.trans location)
    simpa only [Root.location,suspended] using same
  obtain ⟨original,originalAt,originalLocation⟩ := allocated.suspended_origin freshAt freshHome
  exact ⟨original,originalAt,originalLocation.trans (freshLocation.trans location)⟩

namespace Foreign

theorem Mutation.availability {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutation program policy before after) : after.availability = before.availability := by
  cases changed with
  | allocate _ allocated => cases allocated; rfl
  | scalar _ stored => have same := congrArg World.availability stored.2.2.rest; exact same
  | unit _ stored => have same := congrArg World.availability stored.2.rest; exact same
  | pointer _ _ _ _ stored => have same := congrArg World.availability stored.2.rest; exact same
  | aggregate _ _ _ _ constructed => have same := congrArg World.availability constructed.rest; exact same
  | acquire _ _ acquired => exact acquired.availability
  | borrow _ _ borrowed => exact borrowed.availability
  | allocateBuffer _ allocated => cases allocated; rfl
  | reallocateBuffer _ _ reallocated => exact reallocated.availability
  | releaseBuffer _ _ released => exact released.availability
  | rawRead _ _ read => exact read.availability
  | rawWrite _ _ written => exact written.availability
  | rawBorrow _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.availability
  | bulkMove _ _ moved => exact moved.availability
  | retire _ _ retired => cases retired; rfl
  | endLoan ended => cases ended; rfl

theorem Mutations.availability {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutations program policy before after) : after.availability = before.availability := by
  induction changed with
  | refl => rfl
  | cons first _ ih => exact ih.trans first.availability

/-- Every host mutation preserves a suspended root's complete location,
without requiring its current value or incoming references to be private. -/
theorem Mutation.suspended_location {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {id suspension : Identity} {root : Root}
    (changed : Mutation program policy before after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (home : root.home = .suspended suspension) :
    (after.roots.get id).map Root.location = some root.location := by
  have framed (locations : ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location) :
      (after.roots.get id).map Root.location = some root.location := by simpa only [selected,Option.map_some] using locations id
  have exactRoot (same : after.roots.get id = before.roots.get id) :
      (after.roots.get id).map Root.location = some root.location := by rw [same,selected]; rfl
  have internalHome : InternalHome root := by intro domain; simp [home]
  cases changed with
  | allocate _ allocated => exact exactRoot (allocated.roots_other bound)
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
  | reallocateBuffer _ _ reallocated => exact exactRoot (reallocated.private_root bound selected internalHome)
  | @releaseBuffer pointer domain _ _ released =>
    have origin : ∃ allocation, pointer.allocation = some allocation := by cases released; exact ⟨_,by assumption⟩
    obtain ⟨allocation,origin⟩ := origin
    exact exactRoot (released.roots_other origin (released.avoids_internal selected internalHome origin).symm)
  | rawRead _ _ read =>
    cases read with
    | read _ _ _ action =>
      rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
      · exact framed copied.locations
      · exact framed moved.locations
  | rawWrite _ _ written => cases written with | write _ _ _ _ _ moved => exact framed moved.locations
  | rawBorrow _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact framed formed.locations
  | bulkMove _ _ moved =>
    obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
    exact framed (fun key => (installed.locations key).trans (cleared.locations key))
  | retire _ _ retired => exact retired.suspended_location selected home
  | endLoan ended => cases ended; exact exactRoot rfl

theorem Mutations.suspended_location {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {id suspension : Identity} {root : Root}
    (changed : Mutations program policy before after) (bound : id < before.nextRoot)
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
    {id suspension : Identity} {root : Root}
    (changed : Mutation program policy before after)
    (noSuspendedHome : ∀ home region, policy.home home region → ∀ sid, home ≠ .suspended sid)
    (selected : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  have framed (locations : ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location) :=
    World.root_origin_of_locations (locations id) selected
  cases changed with
  | allocate admitted allocated => exact allocated.suspended_origin (noSuspendedHome _ _ admitted _) selected home
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
  | reallocateBuffer _ _ reallocated => exact reallocated.suspended_origin selected home
  | releaseBuffer _ _ released => exact released.suspended_origin selected home
  | rawRead _ _ read =>
    cases read with
    | read _ _ _ action =>
      rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
      · exact framed copied.locations
      · exact framed moved.locations
  | rawWrite _ _ written => cases written with | write _ _ _ _ _ moved => exact framed moved.locations
  | rawBorrow _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact framed formed.locations
  | bulkMove _ _ moved =>
    obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
    exact framed (fun key => (installed.locations key).trans (cleared.locations key))
  | retire _ _ retired => exact retired.suspended_origin selected home
  | endLoan ended => cases ended; exact ⟨root,selected,rfl⟩

theorem Mutations.suspended_origin {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {id suspension : Identity} {root : Root}
    (changed : Mutations program policy before after)
    (noSuspendedHome : ∀ home region, policy.home home region → ∀ sid, home ≠ .suspended sid)
    (selected : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  induction changed generalizing root with
  | refl => exact ⟨root,selected,rfl⟩
  | cons first _ ih =>
    obtain ⟨current,currentAt,location⟩ := ih selected home
    have currentHome : current.home = .suspended suspension := by
      simpa only [Root.location,home] using congrArg Root.home location
    obtain ⟨original,originalAt,originalLocation⟩ := first.suspended_origin noSuspendedHome currentAt currentHome
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
    {observation next : List Nat} {action : HostAction} {id suspension : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next)
    (rootAt : before.roots.get id = some root) (home : root.home = .suspended suspension) (live : root.live = true) :
    before.nextRoot ≤ after.nextRoot ∧ after.availability = before.availability ∧
    ∃ current, after.roots.get id = some current ∧ current.location = root.location ∧
      current.home = .suspended suspension ∧ current.live = true := by
  have changed := (lawful.step _ _ _ _ _ _ _ _ selected well active step).1
  obtain ⟨current,found,location⟩ := Option.map_eq_some_iff.mp
    (changed.suspended_location (World.root_bound well rootAt) rootAt home)
  have sameHome : current.home = root.home := by simpa only [Root.location] using congrArg Root.home location
  have sameLive : current.live = root.live := by simpa only [Root.location] using congrArg Root.live location
  exact ⟨changed.homeExtension.counter,changed.availability,current,found,location,sameHome.trans home,sameLive.trans live⟩

/-- No post-step suspension root is accepted as a new inventory certificate:
the host law and its concrete mutation sequence produce its predecessor. -/
theorem Model.Lawful.host_suspended_origin {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {action : HostAction} {id suspension : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next)
    (rootAt : after.roots.get id = some root) (home : root.home = .suspended suspension) :
    ∃ original, before.roots.get id = some original ∧ original.location = root.location := by
  have changed := (lawful.step _ _ _ _ _ _ _ _ selected well active step).1
  exact changed.suspended_origin (fun _ _ admitted sid => Policy.no_suspended_home admitted sid) rootAt home

end Foreign
end Glorious.Language
