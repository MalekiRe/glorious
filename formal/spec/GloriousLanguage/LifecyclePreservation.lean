import GloriousLanguage.PointerPreservation
import GloriousLanguage.ClearPreservation
import GloriousLanguage.ResidentMutationPreservation
import GloriousLanguage.LoanPreservation

/-! General preservation through storage retirement, loan release and region
closure. These are the actual teardown relations used by cleanup and
cancellation; no well-formed or typed post-state is an admission premise. -/
namespace Glorious.Language



theorem Retires.roots_other {before after : World} {id : Identity}
    (retired : Retires before id after) {other : Identity} (different : other ≠ id) :
    after.roots.get other = before.roots.get other := by
  cases retired
  exact Table.get_set_other _ _ _ _ different

theorem Retires.live_root {before after : World} {id other : Identity} {root : Root}
    (retired : Retires before id after) (found : after.roots.get other = some root) (live : root.live = true) :
    before.roots.get other = some root := by
  cases retired with
  | vacant _ _ _ _ =>
      by_cases same : other = id
      · subst other
        simp only [Table.get_set] at found
        cases found
        cases live
      · simpa only [Table.get_set_other _ _ _ _ same] using found


theorem Retires.resident {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} {value : Value} : after.Resident address value ↔ before.Resident address value := by
  simp only [World.resident_iff_stores,World.Stores,retired.read]

theorem Retires.root_other {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} (different : address.root ≠ id) : after.root address = before.root address := by
  simp only [World.root,retired.roots_other different]

theorem Retires.located {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} (different : address.root ≠ id) (located : before.Located address) : after.Located address := by
  rcases located with ⟨value,stored⟩ | ⟨root,found,vacant⟩
  · exact Or.inl ⟨value,by simpa only [World.Stores,retired.read] using stored⟩
  · exact Or.inr ⟨root,by simpa only [retired.root_other different] using found,vacant⟩

theorem Retires.wellFormed {before after : World} {id : Identity}
    (valid : before.WellFormed) (retired : Retires before id after) : after.WellFormed := by
  have residents := fun {address value} => (retired.resident (address := address) (value := value)).mp
  have liveRoots := fun {other root} => retired.live_root (other := other) (root := root)
  have rootFrame := fun {address} => retired.root_other (address := address)
  have locations := fun {address} => retired.located (address := address)
  cases retired with
  | vacant selected _ _ safe =>
      rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
        roots,regions,bases,ranges,loans,references,overlaps,parents,located,guards⟩
      refine ⟨rootUnique.set _ _,loanUnique,proofUnique,regionUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,parents,?_,guards⟩
      · intro key available found
        obtain ⟨identity,bound,brand,active,recorded⟩ := proofs key available found
        refine ⟨identity,bound,brand,fun live => ⟨(active live).1,?_⟩,recorded⟩
        intro place member
        simpa only [rootFrame (safe.2.1 key available found live place member)] using (active live).2 place member
      · exact fun address value pack resident head => packs address value pack (residents resident) head
      · exact fun address value resident => owners address value (residents resident)
      · exact fun a b x y first second same => ownerUnique a b x y (residents first) (residents second) same
      · intro key root found
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          obtain ⟨bound,_,layout,bytes,bounds⟩ := roots id _ selected
          exact ⟨bound,by simp,layout,bytes,bounds⟩
        · exact roots key root (by simpa only [Table.get_set_other _ _ _ _ same] using found)
      · exact fun key root found live => bases key root (liveRoots found live) live
      · exact fun a b left right first second different leftLive rightLive =>
          ranges a b left right (liveRoots first leftLive) (liveRoots second rightLive) different leftLive rightLive
      · intro key loan found
        obtain ⟨identity,bound,active⟩ := loans key loan found
        refine ⟨identity,bound,fun live => ⟨(active live).1,?_⟩⟩
        simpa only [rootFrame (safe.1 key loan found live)] using (active live).2
      · exact fun address value key resident head => references address value key (residents resident) head
      · intro a b left right first second leftLive rightLive overlap unique
        rcases overlaps a b left right first second leftLive rightLive overlap unique with ancestry | ancestry
        · exact Or.inl (ancestry.transport (before := before) (by rfl))
        · exact Or.inr (ancestry.transport (before := before) (by rfl))
      · exact fun key loan found live => locations (safe.1 key loan found live) (located key loan found live)

theorem Retires.worldTyped {program : Kernel.Program} {before after : World} {id : Identity}
    (typed : Typing.WorldTyped program before) (retired : Retires before id after) : Typing.WorldTyped program after := by
  refine ⟨retired.wellFormed typed.1,?_,?_,?_⟩
  · intro address value resident
    have original := retired.resident.mp resident
    apply (typed.2.1 address value original).resident_transport ?_ ?_ (fun _ origin => origin.retire retired) ⟨address,original⟩
    · intro key loan _ found live
      have safe : loan.referent.root ≠ id := by
        cases retired with
        | vacant _ _ _ allowed => exact allowed.1 key loan found live
      refine ⟨?_,fun _ type => type.retained (fun _ selected => ?_) retired.read⟩
      · cases retired
        exact found
      · simpa only [retired.roots_other safe] using selected
    · cases retired
      rfl
  · intro key root value found contents
    cases retired with
    | vacant _ _ empty _ =>
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          simp [empty] at contents
        · exact typed.2.2.1 key root value (by simpa only [Table.get_set_other _ _ _ _ same] using found) contents
  · intro key root found
    cases retired with
    | vacant selected _ _ _ =>
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          have supported := typed.2.2.2 id _ selected
          exact supported
        · exact typed.2.2.2 key root (by simpa only [Table.get_set_other _ _ _ _ same] using found)

theorem EndsLoan.live_origin {program : RuntimeProgram} {before after : World} {id key : Identity} {loan : Loan}
    (ended : EndsLoan program before id after) (found : after.loans.get key = some loan) (live : loan.live = true) :
    before.loans.get key = some loan := by
  cases ended with
  | restored _ _ _ _ _ _ _ _ =>
      by_cases same : key = id
      · subst key
        simp only [Table.get_set] at found
        cases found
        cases live
      · simpa only [Table.get_set_other _ _ _ _ same] using found

theorem AncestorLoan.endLoan {program : RuntimeProgram} {before after : World} {id ancestor child : Identity}
    (ended : EndsLoan program before id after) (related : AncestorLoan before ancestor child) : AncestorLoan after ancestor child := by
  cases ended with
  | restored selected _ _ _ _ _ _ _ =>
      induction related with
      | refl => exact .refl
      | @parent parent child loan found link _ ih =>
          by_cases same : child = id
          · subst child
            have equal := Option.some.inj (selected.symm.trans found)
            subst loan
            exact .parent (Table.get_set _ _ _) link ih
          · exact .parent (by simpa only [Table.get_set_other _ _ _ _ same] using found) link ih


namespace Execution

theorem RegionEnds.wellFormed {before after : World} {region : Identity}
    (valid : before.WellFormed) (ended : RegionEnds before region after) : after.WellFormed := by
  obtain ⟨⟨noRoots,noLoans,noProofs,noPacks⟩,rfl⟩ := ended
  rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations,guards⟩
  refine ⟨rootUnique,loanUnique,proofUnique,regionUnique.filter _,?_,?_,owners,ownerUnique,?_,?_,bases,ranges,?_,references,?_,parents,locations,guards⟩
  · intro id available found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available found
    refine ⟨identity,bound,brand,fun live => ⟨?_,(active live).2⟩,recorded⟩
    simpa using And.intro (active live).1 (noProofs id available found live)
  · intro address value pack resident head
    obtain ⟨bound,live,length,distinct,facts⟩ := packs address value pack resident head
    refine ⟨bound,?_,length,distinct,facts⟩
    simpa using And.intro live (noPacks address value pack resident head)
  · intro id root found
    obtain ⟨bound,active,layout,bytes,bounds⟩ := roots id root found
    refine ⟨bound,fun live => ?_,layout,bytes,bounds⟩
    simpa using And.intro (active live) (noRoots id root found live)
  · intro id member
    exact regions id (List.mem_filter.mp member).1
  · intro id loan found
    obtain ⟨identity,bound,active⟩ := loans id loan found
    refine ⟨identity,bound,fun live => ⟨?_,(active live).2⟩⟩
    simpa using And.intro (active live).1 (noLoans id loan found live)
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun related => related.transport (before := before) (after := { before with liveRegions := before.liveRegions.filter (· != region) }) rfl)
      (fun related => related.transport (before := before) (after := { before with liveRegions := before.liveRegions.filter (· != region) }) rfl)

theorem RegionEnds.worldTyped {program : Kernel.Program} {before after : World} {region : Identity}
    (typed : Typing.WorldTyped program before) (ended : RegionEnds before region after) : Typing.WorldTyped program after := by
  have valid := ended.wellFormed typed.1
  obtain ⟨_,rfl⟩ := ended
  refine ⟨valid,?_,typed.2.2⟩
  intro address value resident
  apply (typed.2.1 address value resident).resident_transport ?_ ?_ ?_ ⟨address,resident⟩
  · intro id loan _ found _
    exact ⟨found,fun _ type => type.retained (fun _ selected => selected) (fun _ => rfl)⟩
  · rfl
  · exact fun _ origin => origin

end Execution

theorem CanEndStorage.owner_permission {world : World} {id : Identity} {root : Root}
    (safe : CanEndStorage world id) (found : world.roots.get id = some root) (live : root.live = true) :
    Permitted world .owner .owned ⟨id,root.generation,[]⟩ := by
  refine ⟨⟨root,by simp [World.root,found,live]⟩,?_⟩
  intro key loan selected active overlap _
  exact safe.1 key loan selected active overlap.1.symm

theorem CanEndStorage.place_permission {world : World} {address : Address} {root : Root}
    (safe : CanEndStorage world address.root) (whole : address.fields = [])
    (selected : world.root address = some root) : Permitted world .owner .owned address := by
  obtain ⟨found,live,generation⟩ := World.root_found selected
  have permission := safe.owner_permission found live
  have same : address = ⟨address.root,root.generation,[]⟩ := by
    cases address
    simp_all
  simpa only [← same] using permission

theorem Memory.ReleasesBuffer.wellFormed {program : Program} {before after : World} {pointer : RawPointer} {domain : Identity}
    {allocation : ResolvedPlace}
    (valid : before.WellFormed) (released : Memory.ReleasesBuffer program before allocation pointer domain after) : after.WellFormed := by
  cases released with
  | release _ selected _ _ _ claims safe written retired closed =>
      exact closed.wellFormed (retired.wellFormed
        (World.clear_wellFormed (claims.wellFormed valid)
          (safe.place_permission claims.ready.whole (by cases claims; exact selected)) written))

theorem Memory.ReleasesBuffer.worldTyped {program : Kernel.Program} {before after : World} {pointer : RawPointer} {domain : Identity}
    {allocation : ResolvedPlace}
    (typed : Typing.WorldTyped program before) (released : Memory.ReleasesBuffer program.declarations before allocation pointer domain after) :
    Typing.WorldTyped program after := by
  cases released with
  | release _ selected _ _ _ claims safe written retired closed =>
      exact closed.worldTyped (retired.worldTyped
        (World.clear_worldTyped (claims.worldTyped typed)
          (safe.place_permission claims.ready.whole (by cases claims; exact selected)) written))

theorem Execution.RetiresEmpty.worldTyped {program : Kernel.Program} {before after : World} {addresses : List Address}
    (typed : Typing.WorldTyped program before) (retired : Execution.RetiresEmpty before addresses after) :
    Typing.WorldTyped program after := by
  induction retired with
  | nil => exact typed
  | cons _ first _ ih => exact ih (first.worldTyped typed)


end Glorious.Language
