import GloriousLanguage.PatternTransport
import GloriousLanguage.RuntimeTypingEquivariance

/-! Whole-world runtime-region renaming for universally quantified code
coverage. It transforms the existing storage product, never a second heap or
an assumed well-typed result, and preserves all non-region identities. -/
namespace Glorious.Language

def RegionPermutation.bound (permutation : RegionPermutation) (bound : Identity) : Identity :=
  (List.range bound).foldr (fun id next => max (permutation.rename id+1) next) 0

theorem RegionPermutation.rename_below_bound (permutation : RegionPermutation) {id bound : Identity}
    (below : id < bound) : permutation.rename id < permutation.bound bound := by
  have member := List.mem_range.mpr below
  have upper (values : List Identity) : ∀ id ∈ values,
      permutation.rename id+1 ≤ values.foldr (fun id next => max (permutation.rename id+1) next) 0 := by
    induction values with
    | nil => intro id impossible; cases impossible
    | cons first rest ih =>
      intro id member
      rcases List.mem_cons.mp member with rfl | present
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih id present) (Nat.le_max_right _ _)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (upper _ _ member)

def RegionPermutation.head (permutation : RegionPermutation) : ValueHead → ValueHead
  | .callable id arguments => .callable id (arguments.map permutation.term)
  | .operation id arguments => .operation id (arguments.map permutation.term)
  | .bindings pack => .bindings { pack with region := permutation.rename pack.region }
  | head => head

/- Erased resource obligations carry root/generation identities and loan
authorities, never runtime regions, so region renaming retains them verbatim. -/
mutual
  def RegionPermutation.value (permutation : RegionPermutation) : Value → Value
    | .resident owner type head live fields resources =>
        .resident owner (permutation.term type) (permutation.head head) live (permutation.values fields) resources

  def RegionPermutation.values (permutation : RegionPermutation) : List (Option Value) → List (Option Value)
    | [] => []
    | none :: rest => none :: permutation.values rest
    | some value :: rest => some (permutation.value value) :: permutation.values rest
end

def RegionPermutation.root (permutation : RegionPermutation) (root : Root) : Root :=
  { root with region := permutation.rename root.region, type := permutation.term root.type, value := root.value.map permutation.value }

def RegionPermutation.loan (permutation : RegionPermutation) (loan : Loan) : Loan :=
  { loan with region := permutation.rename loan.region }

def RegionPermutation.availability (permutation : RegionPermutation) (available : Availability) : Availability :=
  { available with
    brand := permutation.term available.brand
    region := permutation.rename available.region
    residents := available.residents.map permutation.term }

def RegionPermutation.world (permutation : RegionPermutation) (world : World) : World :=
  { world with
    roots := world.roots.map (fun (id,root) => (id,permutation.root root))
    loans := world.loans.map (fun (id,loan) => (id,permutation.loan loan))
    availability := world.availability.map (fun (id,available) => (id,permutation.availability available))
    liveRegions := world.liveRegions.map permutation.rename
    nextRegion := permutation.bound world.nextRegion }

theorem RegionPermutation.head_involutive (permutation : RegionPermutation) (head : ValueHead) :
    permutation.head (permutation.head head) = head := by
  cases head <;> simp only [RegionPermutation.head,List.map_map,Function.comp_def,
    permutation.term_involutive,List.map_id',permutation.involutive]

mutual
  theorem RegionPermutation.value_involutive (permutation : RegionPermutation) (value : Value) :
      permutation.value (permutation.value value) = value := by
    cases value with
    | resident owner type head live fields resources =>
      simp only [RegionPermutation.value,permutation.term_involutive,permutation.head_involutive,
        permutation.values_involutive fields]
  termination_by sizeOf value

  theorem RegionPermutation.values_involutive (permutation : RegionPermutation) (values : List (Option Value)) :
      permutation.values (permutation.values values) = values := by
    cases values with
    | nil => rfl
    | cons first rest =>
      cases first with
      | none => simp only [RegionPermutation.values,permutation.values_involutive rest]
      | some value => simp only [RegionPermutation.values,permutation.value_involutive value,permutation.values_involutive rest]
  termination_by sizeOf values
end

theorem RegionPermutation.values_map (permutation : RegionPermutation) (values : List (Option Value)) :
    permutation.values values = values.map (Option.map permutation.value) := by
  induction values with
  | nil => rfl
  | cons first rest ih => cases first <;> simp only [RegionPermutation.values,List.map_cons,Option.map,ih]

theorem RegionPermutation.value_owner (permutation : RegionPermutation) (value : Value) : (permutation.value value).owner = value.owner := by
  cases value; rfl

theorem RegionPermutation.value_type (permutation : RegionPermutation) (value : Value) : (permutation.value value).type = permutation.term value.type := by
  cases value; rfl

theorem RegionPermutation.value_head (permutation : RegionPermutation) (value : Value) : (permutation.value value).head = permutation.head value.head := by
  cases value; rfl

theorem RegionPermutation.value_live (permutation : RegionPermutation) (value : Value) : (permutation.value value).shellLive = value.shellLive := by
  cases value; rfl

theorem RegionPermutation.value_fields (permutation : RegionPermutation) (value : Value) :
    (permutation.value value).fields = value.fields.map (Option.map permutation.value) := by
  cases value
  exact permutation.values_map _

theorem RegionPermutation.value_atPath (permutation : RegionPermutation) (value : Value) (path : List Nat) :
    (permutation.value value).atPath path = (value.atPath path).map permutation.value := by
  induction path generalizing value with
  | nil => rfl
  | cons index rest ih =>
    simp only [Value.atPath,permutation.value_fields,List.getElem?_map]
    cases value.fields[index]? with
    | none => rfl
    | some field =>
      cases field with
      | none => rfl
      | some child => exact ih child

theorem RegionPermutation.residentAt (permutation : RegionPermutation) {whole value : Value} {path : List Nat}
    (resident : ResidentAt whole path value) : ResidentAt (permutation.value whole) path (permutation.value value) := by
  induction resident with
  | root => exact .root
  | field selected _ ih =>
    exact .field (by rw [permutation.value_fields,List.getElem?_map,selected]; rfl) ih

theorem RegionPermutation.residentAt_origin (permutation : RegionPermutation) {whole value : Value} {path : List Nat}
    (resident : ResidentAt (permutation.value whole) path value) :
    ∃ original, ResidentAt whole path original ∧ value = permutation.value original := by
  have original := permutation.residentAt resident
  rw [permutation.value_involutive] at original
  exact ⟨permutation.value value,original,(permutation.value_involutive value).symm⟩

theorem RegionPermutation.value_initialized (permutation : RegionPermutation) {value : Value}
    (initialized : value.Initialized) : (permutation.value value).Initialized := by
  intro path resident inside
  obtain ⟨original,selected,rfl⟩ := permutation.residentAt_origin inside
  refine ⟨by rw [permutation.value_live]; exact (initialized path original selected).1,?_⟩
  intro field member
  rw [permutation.value_fields] at member
  obtain ⟨oldField,present,rfl⟩ := List.mem_map.mp member
  simpa only [Option.isSome_map] using (initialized path original selected).2 oldField present

theorem RegionPermutation.world_roots (permutation : RegionPermutation) (world : World) (id : Identity) :
    (permutation.world world).roots.get id = (world.roots.get id).map permutation.root :=
  Table.get_map_values _ _ _

theorem RegionPermutation.world_loans (permutation : RegionPermutation) (world : World) (id : Identity) :
    (permutation.world world).loans.get id = (world.loans.get id).map permutation.loan :=
  Table.get_map_values _ _ _

theorem RegionPermutation.world_availability (permutation : RegionPermutation) (world : World) (id : Identity) :
    (permutation.world world).availability.get id = (world.availability.get id).map permutation.availability :=
  Table.get_map_values _ _ _

theorem RegionPermutation.world_root (permutation : RegionPermutation) (world : World) (address : Address) :
    (permutation.world world).root address = (world.root address).map permutation.root := by
  simp only [World.root,permutation.world_roots]
  cases world.roots.get address.root with
  | none => rfl
  | some root =>
    dsimp only [Option.map,Bind.bind,Option.bind,RegionPermutation.root]
    split <;> rfl

theorem RegionPermutation.world_read (permutation : RegionPermutation) (world : World) (address : Address) :
    (permutation.world world).read address = (world.read address).map permutation.value := by
  simp only [World.read,permutation.world_root]
  cases world.root address with
  | none => rfl
  | some root =>
    dsimp only [Option.map,Bind.bind,Option.bind,RegionPermutation.root]
    cases stored : root.value with
    | none => rfl
    | some value => exact permutation.value_atPath value address.fields

theorem RegionPermutation.stores (permutation : RegionPermutation) {world : World} {address : Address} {value : Value}
    (stored : world.Stores address value) : (permutation.world world).Stores address (permutation.value value) := by
  change world.read address = some value at stored
  change (permutation.world world).read address = some _
  rw [permutation.world_read,stored]; rfl

theorem RegionPermutation.stores_origin (permutation : RegionPermutation) {world : World} {address : Address} {value : Value}
    (stored : (permutation.world world).Stores address value) :
    ∃ original, world.Stores address original ∧ value = permutation.value original := by
  change (permutation.world world).read address = some value at stored
  rw [permutation.world_read] at stored
  obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp stored
  exact ⟨original,found,same.symm⟩

theorem RegionPermutation.resident (permutation : RegionPermutation) {world : World} {address : Address} {value : Value}
    (resident : world.Resident address value) : (permutation.world world).Resident address (permutation.value value) := by
  obtain ⟨root,whole,found,live,generation,stored,inside⟩ := resident
  exact ⟨permutation.root root,permutation.value whole,by rw [permutation.world_roots,found]; rfl,
    live,generation,by simp only [RegionPermutation.root,stored,Option.map],permutation.residentAt inside⟩

theorem RegionPermutation.resident_origin (permutation : RegionPermutation) {world : World} {address : Address} {value : Value}
    (resident : (permutation.world world).Resident address value) :
    ∃ original, world.Resident address original ∧ value = permutation.value original := by
  obtain ⟨root,whole,found,live,generation,stored,inside⟩ := resident
  rw [permutation.world_roots] at found
  obtain ⟨oldRoot,selected,rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨oldWhole,oldStored,rfl⟩ := Option.map_eq_some_iff.mp stored
  obtain ⟨original,atOriginal,rfl⟩ := permutation.residentAt_origin inside
  exact ⟨original,⟨oldRoot,oldWhole,selected,live,generation,oldStored,atOriginal⟩,rfl⟩

theorem RegionPermutation.vacant (permutation : RegionPermutation) {world : World} {address : Address}
    (vacant : world.Vacant address) : (permutation.world world).Vacant address := by
  obtain ⟨root,found,empty | ⟨parent,index,value,path,stored,container,selected,hole⟩⟩ := vacant
  · exact ⟨permutation.root root,by rw [permutation.world_root,found]; rfl,
      Or.inl ⟨empty.1,by simp only [RegionPermutation.root,empty.2,Option.map_none]⟩⟩
  · refine ⟨permutation.root root,by rw [permutation.world_root,found]; rfl,
      Or.inr ⟨parent,index,permutation.value value,path,?_,permutation.value container,?_,?_⟩⟩
    · simp only [RegionPermutation.root,stored,Option.map_some]
    · rw [permutation.value_atPath,selected]; rfl
    · rw [permutation.value_fields,List.getElem?_map,hole]; rfl

theorem RegionPermutation.located (permutation : RegionPermutation) {world : World} {address : Address}
    (located : world.Located address) : (permutation.world world).Located address := by
  rcases located with ⟨value,stored⟩ | vacant
  · exact Or.inl ⟨permutation.value value,permutation.stores stored⟩
  · exact Or.inr (permutation.vacant vacant)

theorem RegionPermutation.ancestorLoan (permutation : RegionPermutation) {world : World} {first last : Identity}
    (ancestor : AncestorLoan world first last) : AncestorLoan (permutation.world world) first last := by
  induction ancestor with
  | refl => exact .refl
  | @parent parent child loan found selected _ ih =>
    exact .parent (loan := permutation.loan loan) (by rw [permutation.world_loans,found]; rfl) selected ih

theorem RegionPermutation.ancestorLoan_origin (permutation : RegionPermutation) {world : World} {first last : Identity}
    (ancestor : AncestorLoan (permutation.world world) first last) : AncestorLoan world first last := by
  induction ancestor with
  | refl => exact .refl
  | parent found parent _ ih =>
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    exact .parent oldFound parent ih

/-- A rentable region permutation retains every loan identity, referent,
generation, mode and guard list, so the full permission product transports in
both directions, including the live-guard and shared-guard obligations. -/
theorem RegionPermutation.loanPermission_iff (permutation : RegionPermutation) {world : World}
    {id : Identity} {requested : Access} {address : Address} :
    LoanPermission (permutation.world world) id requested address ↔
      LoanPermission world id requested address := by
  constructor
  · rintro ⟨active,selected,live,rootEq,generation,path,mode,allowed,guardLives,guardShared⟩
    rw [permutation.world_loans] at selected
    obtain ⟨original,oldSelected,rfl⟩ := Option.map_eq_some_iff.mp selected
    refine ⟨original,oldSelected,live,rootEq,generation,path,mode,?_,?_,?_⟩
    · intro other loan found live different overlaps conflict
      exact permutation.ancestorLoan_origin (allowed other (permutation.loan loan)
        (by rw [permutation.world_loans,found]; rfl) live different overlaps conflict)
    · intro guard member
      obtain ⟨carrier,found,live⟩ := guardLives guard member
      rw [permutation.world_loans] at found
      obtain ⟨oldCarrier,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨oldCarrier,oldFound,live⟩
    · intro other loan found live member
      exact guardShared other (permutation.loan loan) (by rw [permutation.world_loans,found]; rfl) live member
  · rintro ⟨active,selected,live,rootEq,generation,path,mode,allowed,guardLives,guardShared⟩
    refine ⟨permutation.loan active,by rw [permutation.world_loans,selected]; rfl,live,rootEq,generation,path,mode,?_,?_,?_⟩
    · intro other loan found live different overlaps conflict
      rw [permutation.world_loans] at found
      obtain ⟨oldLoan,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact permutation.ancestorLoan (allowed other oldLoan oldFound live different overlaps conflict)
    · intro guard member
      obtain ⟨carrier,found,live⟩ := guardLives guard member
      exact ⟨permutation.loan carrier,by rw [permutation.world_loans,found]; rfl,live⟩
    · intro other loan found live member
      rw [permutation.world_loans] at found
      obtain ⟨oldLoan,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact guardShared other oldLoan oldFound live member

theorem RegionPermutation.permitted_iff (permutation : RegionPermutation) {world : World}
    {authority : Authority} {access : Access} {address : Address} :
    Permitted (permutation.world world) authority access address ↔ Permitted world authority access address := by
  induction authority with
  | owner =>
    constructor
    · rintro ⟨⟨root,found⟩,allowed⟩
      rw [permutation.world_root] at found
      obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨⟨original,oldFound⟩,fun id loan selected live overlaps =>
        allowed id (permutation.loan loan) (by rw [permutation.world_loans,selected]; rfl) live overlaps⟩
    · rintro ⟨⟨root,found⟩,allowed⟩
      refine ⟨⟨permutation.root root,by rw [permutation.world_root,found]; rfl⟩,?_⟩
      intro id loan selected live overlaps
      rw [permutation.world_loans] at selected
      obtain ⟨original,oldSelected,rfl⟩ := Option.map_eq_some_iff.mp selected
      exact allowed id original oldSelected live overlaps
  | loan id =>
    constructor
    · rintro ⟨⟨root,found⟩,permitted⟩
      rw [permutation.world_root] at found
      obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨⟨original,oldFound⟩,permutation.loanPermission_iff.mp permitted⟩
    · rintro ⟨⟨root,found⟩,permitted⟩
      exact ⟨⟨permutation.root root,by rw [permutation.world_root,found]; rfl⟩,
        permutation.loanPermission_iff.mpr permitted⟩
  | shared backing ih =>
    constructor
    · rintro ⟨⟨root,found⟩,access,evidence⟩
      rw [permutation.world_root] at found
      obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨⟨original,oldFound⟩,access,ih.mp evidence⟩
    · rintro ⟨⟨root,found⟩,access,evidence⟩
      exact ⟨⟨permutation.root root,by rw [permutation.world_root,found]; rfl⟩,access,ih.mpr evidence⟩
  | guarded backing carrier ih =>
    constructor
    · rintro ⟨⟨root,found⟩,backing,loan,selected,permitted⟩
      rw [permutation.world_root] at found
      obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
      rw [permutation.world_loans] at selected
      obtain ⟨carrierLoan,oldSelected,rfl⟩ := Option.map_eq_some_iff.mp selected
      exact ⟨⟨original,oldFound⟩,ih.mp backing,carrierLoan,oldSelected,
        permutation.loanPermission_iff.mp permitted⟩
    · rintro ⟨⟨root,found⟩,backing,loan,selected,permitted⟩
      refine ⟨⟨permutation.root root,by rw [permutation.world_root,found]; rfl⟩,ih.mpr backing,
        permutation.loan loan,by rw [permutation.world_loans,selected]; rfl,?_⟩
      exact permutation.loanPermission_iff.mpr permitted

theorem RegionPermutation.injective (permutation : RegionPermutation) : Function.Injective permutation.rename := by
  intro first second equal
  have same := congrArg permutation.rename equal
  simpa only [permutation.involutive] using same

theorem RegionPermutation.world_wellFormed (permutation : RegionPermutation) {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) : (permutation.world world).WellFormedWithOrigins originBound := by
  rcases valid with ⟨roots,loans,proofs,regions,available,packs,owners,exclusive,rootBounds,regionBounds,
    aligned,disjoint,loanBounds,references,overlaps,parents,locations,guards,kinds⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [RegionPermutation.world,Table.Unique,List.map_map,Function.comp_def] using roots
  · simpa only [RegionPermutation.world,Table.Unique,List.map_map,Function.comp_def] using loans
  · simpa only [RegionPermutation.world,Table.Unique,List.map_map,Function.comp_def] using proofs
  · exact List.pairwise_map.mpr (regions.imp (fun different same => different (permutation.injective same)))
  · intro id proof found
    rw [permutation.world_availability] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨identity,bound,brand,active,recorded⟩ := available id original oldFound
    refine ⟨identity,bound,by simp only [RegionPermutation.availability,brand,RegionPermutation.term,Term.renameRuntimeRegions],?_,?_⟩
    · intro live
      obtain ⟨region,places⟩ := active live
      refine ⟨List.mem_map.mpr ⟨_,region,rfl⟩,?_⟩
      intro place member
      rw [permutation.world_root,Option.isSome_map]
      exact places place member
    · intro place member
      apply (recorded place member).transport
      intro id loan found
      exact ⟨permutation.loan loan,by rw [permutation.world_loans,found]; rfl⟩
  · intro address value pack resident head
    obtain ⟨original,oldResident,rfl⟩ := permutation.resident_origin resident
    rw [permutation.value_head] at head
    have originalHead := congrArg permutation.head head
    rw [permutation.head_involutive] at originalHead
    obtain ⟨brand,region,length,distinct,facts⟩ := packs address original _ oldResident originalHead
    refine ⟨brand,?_,?_,distinct,facts⟩
    · exact List.mem_map.mpr ⟨permutation.rename pack.region,region,permutation.involutive pack.region⟩
    · simpa only [RegionPermutation.value_fields,List.length_map,RegionPermutation.head] using length
  · intro address value resident
    obtain ⟨original,oldResident,rfl⟩ := permutation.resident_origin resident
    rw [permutation.value_owner]
    exact owners address original oldResident
  · intro a b x y first second same
    obtain ⟨left,oldFirst,rfl⟩ := permutation.resident_origin first
    obtain ⟨right,oldSecond,rfl⟩ := permutation.resident_origin second
    exact exclusive a b left right oldFirst oldSecond (by simpa only [permutation.value_owner] using same)
  · intro id root found
    rw [permutation.world_roots] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨bound,live,layout,bytes,contents⟩ := rootBounds id original oldFound
    exact ⟨bound,fun evidence => List.mem_map.mpr ⟨_,live evidence,rfl⟩,layout,bytes,contents⟩
  · intro region member
    obtain ⟨original,oldMember,rfl⟩ := List.mem_map.mp member
    exact permutation.rename_below_bound (regionBounds original oldMember)
  · intro id root found live
    rw [permutation.world_roots] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    exact aligned id original oldFound live
  · intro a b left right first second different liveLeft liveRight
    rw [permutation.world_roots] at first second
    obtain ⟨originalLeft,oldFirst,rfl⟩ := Option.map_eq_some_iff.mp first
    obtain ⟨originalRight,oldSecond,rfl⟩ := Option.map_eq_some_iff.mp second
    exact disjoint a b originalLeft originalRight oldFirst oldSecond different liveLeft liveRight
  · intro id loan found
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨identity,bound,live⟩ := loanBounds id original oldFound
    refine ⟨identity,bound,?_⟩
    intro evidence
    exact ⟨List.mem_map.mpr ⟨_,(live evidence).1,rfl⟩,
      by rw [permutation.world_root,Option.isSome_map]; exact (live evidence).2⟩
  · intro address value id resident head
    obtain ⟨original,oldResident,rfl⟩ := permutation.resident_origin resident
    rw [permutation.value_head] at head
    have originalHead := congrArg permutation.head head
    rw [permutation.head_involutive] at originalHead
    obtain ⟨loan,found,live⟩ := references address original id oldResident originalHead
    exact ⟨permutation.loan loan,by rw [permutation.world_loans,found]; rfl,live⟩
  · intro a b left right first second liveLeft liveRight intersect unique
    rw [permutation.world_loans] at first second
    obtain ⟨originalLeft,oldFirst,rfl⟩ := Option.map_eq_some_iff.mp first
    obtain ⟨originalRight,oldSecond,rfl⟩ := Option.map_eq_some_iff.mp second
    exact (overlaps a b originalLeft originalRight oldFirst oldSecond liveLeft liveRight intersect unique).imp
      permutation.ancestorLoan permutation.ancestorLoan
  · intro id loan parent found selected
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨ancestor,parentFound,bound,contained,mode,live⟩ := parents id original parent oldFound selected
    exact ⟨permutation.loan ancestor,by rw [permutation.world_loans,parentFound]; rfl,bound,contained,mode,live⟩
  · intro id loan found live
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    exact permutation.located (locations id original oldFound live)
  · intro id loan guard found member
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨carrier,carrierFound,bound,live⟩ := guards id original guard oldFound member
    exact ⟨permutation.loan carrier,by rw [permutation.world_loans,carrierFound]; rfl,bound,live⟩
  · intro id loan found
    rw [permutation.world_loans] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    exact kinds id original oldFound

theorem RegionPermutation.fieldLayouts (permutation : RegionPermutation) {program : Program}
    (valid : ProgramWellFormed program) {context : Context} {types : List Term} {layouts : List Layout}
    (located : ListRel (LayoutOf program context) types layouts) :
    ListRel (LayoutOf program (permutation.context context)) (types.map permutation.term) layouts := by
  induction located with
  | nil => exact .nil
  | cons first _ ih => exact .cons (first.permute valid permutation) ih

theorem RegionPermutation.fieldOffset (permutation : RegionPermutation) {program : Program}
    (valid : ProgramWellFormed program) {world : World} {address : Address} {container type : Term} {index offset : Nat}
    (located : FieldOffset program world address container index type offset) :
    FieldOffset program (permutation.world world) address (permutation.term container) index (permutation.term type) offset := by
  induction located <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  case tuple atType layouts aggregate atOffset =>
    exact .tuple (by rw [List.getElem?_map,atType]; rfl) (permutation.fieldLayouts valid layouts) aggregate atOffset
  case bindings atType layouts aggregate atOffset =>
    exact .bindings (by rw [List.getElem?_map,atType]; rfl) (permutation.fieldLayouts valid layouts) aggregate atOffset
  case callable declared atType layouts aggregate atOffset =>
    exact .callable (declared.permute valid permutation) (by rw [List.getElem?_map,atType]; rfl)
      (permutation.fieldLayouts valid layouts) aggregate atOffset
  case array nonnegative bound layout => exact .array nonnegative bound (layout.permute valid permutation)
  case nominal constructor identity instantiated substituted atType layout stored head atOffset =>
    refine .nominal constructor identity (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) (by rw [List.getElem?_map,atType]; rfl)
      (by simpa only [RegionPermutation.context,List.map_nil,RegionPermutation.term,Term.renameRuntimeRegions] using layout.permute valid permutation) (permutation.stores stored)
      (by rw [permutation.value_head,head]; rfl) atOffset
    intro term member
    obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
    exact valid.field_lexical constructor.1 constructor.2.1 present
  case alias found instantiated graph inner ih =>
    exact .alias found (instantiated.permute permutation)
      (permutation.substitutes_lexical (valid.lexical
        (List.mem_of_find?_eq_some (Program.alias_lookup found)) _ (by
          simp only [Definition.terms,List.mem_cons_self])) graph) ih

theorem RegionPermutation.addressOffset (permutation : RegionPermutation) {program : Program}
    (valid : ProgramWellFormed program) {world : World} {address : Address} {type : Term} {offset : Nat}
    (located : AddressOffset program world address type offset) :
    AddressOffset program (permutation.world world) address (permutation.term type) offset := by
  induction located with
  | @root id root found live =>
    exact .root (root := permutation.root root) (by rw [permutation.world_roots,found]; rfl) live
  | child parent field ih => exact .child ih (permutation.fieldOffset valid field)

theorem RegionPermutation.addressType (permutation : RegionPermutation) {program : Program}
    (valid : ProgramWellFormed program) {world : World} {address : Address} {type : Term}
    (located : AddressType program world address type) :
    AddressType program (permutation.world world) address (permutation.term type) :=
  ⟨located.choose,permutation.addressOffset valid located.choose_spec⟩

theorem Execution.ConstructorHead.head_permute {program : Program} {type : Term} {variant : Option DeclId}
    {fields : List Term} {head : ValueHead} (constructed : Execution.ConstructorHead program type variant fields head)
    (permutation : RegionPermutation) : permutation.head head = head := by
  rcases constructed with ⟨_,_,rfl⟩ | ⟨_,_,_,_,_,_,rfl,_⟩ | ⟨_,_,_,_,_,_,_,rfl,_⟩ <;> rfl

theorem RegionPermutation.valueTyped (permutation : RegionPermutation) {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {world : World} {value : Value} (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program (permutation.world world) (permutation.value value) := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => Typing.ValueTyped program (permutation.world world) (permutation.value value))
    (motive_2 := fun fields types _ => Typing.FieldsTyped program (permutation.world world)
      (permutation.values fields) (types.map permutation.term))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals simp only [RegionPermutation.value,RegionPermutation.values,RegionPermutation.term,
    Term.renameRuntimeRegions,RegionPermutation.head,List.map_nil,List.map_cons]
  · intro owner live; exact .unit
  · intro owner value live admissible; exact .scalar admissible
  · intro owner type head live fields types resources constructed _ ih
    have same := constructed.head_permute permutation
    change Typing.ValueTyped program (permutation.world world)
      (.resident owner (permutation.term type) (permutation.head head) live (permutation.values fields) resources)
    rw [same]
    exact .aggregate (constructed.permute valid permutation) ih
  · intro owner mode region type id loan live found active modeEq regionEq located
    exact .reference (loan := permutation.loan loan) (by rw [permutation.world_loans,found]; rfl) active modeEq
      (by simp only [regionEq,Term.renameRuntimeRegions,RegionPermutation.loan]) (permutation.addressType valid located)
  · intro owner mode type pointer live bound origin
    refine .pointer bound ?_
    intro id allocated
    obtain ⟨root,found,address,extent⟩ := origin id allocated
    exact ⟨permutation.root root,by rw [permutation.world_roots,found]; rfl,address,extent⟩
  · intro owner id arguments live fields function instanced _ ih
    have captures : (permutation.function function).captures.map (·.type) = (function.captures.map (·.type)).map permutation.term := by
      simp only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,List.map_map,
        Function.comp_def,Kernel.Local.mapTerms]
    exact .callable (instanced.permute valid inventory permutation) (captures.symm ▸ ih)
  · intro owner id arguments live operation signature instanced
    exact .operation (instanced.permute valid permutation)
  · intro owner brand region result live; exact .label
  · intro owner type id live shape
    obtain ⟨argument,answer,effects,quantity,rfl⟩ := shape
    exact .continuation ⟨permutation.term argument,permutation.term answer,permutation.term effects,quantity,
      by simp only [Term.renameRuntimeRegions,RegionPermutation.term]⟩
  · intro owner brand region residents id live available found brandEq brandRigid regionEq residentsEq
    exact .available (available := permutation.availability available) (by rw [permutation.world_availability,found]; rfl)
      (congrArg permutation.term brandEq) (by simp only [brandRigid,Term.renameRuntimeRegions])
      (by simp only [regionEq,Term.renameRuntimeRegions,RegionPermutation.availability])
      (congrArg (List.map permutation.term) residentsEq)
  · intro owner brand region live fields types pack _ brandEq regionEq length distinct ih
    exact .bindings ih (by simp only [brandEq,Term.renameRuntimeRegions]) (by simp only [regionEq,Term.renameRuntimeRegions])
      (by simpa only [permutation.values_map,List.length_map] using length) distinct
  · exact .nil
  · intro fields type types _ ih; exact .hole ih
  · intro value fields type types _ same _ ihValue ihFields
    exact .resident ihValue (by rw [permutation.value_type,same]; rfl) ihFields

theorem RegionPermutation.worldTyped (permutation : RegionPermutation) {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {world : World} {originBound : Identity} (typed : Typing.WorldTypedWithOrigins program world originBound) :
    Typing.WorldTypedWithOrigins program (permutation.world world) originBound := by
  refine ⟨permutation.world_wellFormed typed.1,?_,?_,?_⟩
  · intro address value resident
    obtain ⟨original,oldResident,rfl⟩ := permutation.resident_origin resident
    exact permutation.valueTyped valid inventory (typed.2.1 address original oldResident)
  · intro id root value found stored
    rw [permutation.world_roots] at found
    obtain ⟨oldRoot,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨oldValue,oldStored,rfl⟩ := Option.map_eq_some_iff.mp stored
    rw [permutation.value_type,typed.2.2.1 id oldRoot oldValue oldFound oldStored]
    rfl
  · intro id root found
    rw [permutation.world_roots] at found
    obtain ⟨original,oldFound,rfl⟩ := Option.map_eq_some_iff.mp found
    exact (typed.2.2.2 id original oldFound).rename permutation.rename (fun _ bound => permutation.rename_below_bound bound)

theorem RegionPermutation.world_read_twice (permutation : RegionPermutation) (world : World) (address : Address) :
    (permutation.world (permutation.world world)).read address = world.read address := by
  rw [permutation.world_read,permutation.world_read,Option.map_map]
  cases world.read address <;> simp only [Option.map,Function.comp_def,permutation.value_involutive]

theorem RegionPermutation.world_loans_twice (permutation : RegionPermutation) (world : World) (id : Identity) :
    (permutation.world (permutation.world world)).loans.get id = world.loans.get id := by
  rw [permutation.world_loans,permutation.world_loans,Option.map_map]
  cases world.loans.get id <;> simp only [Option.map,Function.comp_def,RegionPermutation.loan,permutation.involutive]

theorem RegionPermutation.matches (permutation : RegionPermutation) {program : Program} {world : World}
    {address : Address} {pattern : Kernel.Pattern} (matched : Kernel.Matches program world address pattern) :
    Kernel.Matches program (permutation.world world) address (pattern.mapTerms permutation.term) := by
  refine Kernel.Matches.rec
    (motive_1 := fun address pattern _ => Kernel.Matches program (permutation.world world) address (pattern.mapTerms permutation.term))
    (motive_2 := fun address offset patterns _ => Kernel.MatchesFields program (permutation.world world) address offset
      (patterns.map (Kernel.Pattern.mapTerms permutation.term)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched
  all_goals simp only [Kernel.Pattern.mapTerms,List.map_nil,List.map_cons]
  · intro address; exact .wildcard
  · intro address localSlot value stored initialized; exact .bind (permutation.stores stored) (permutation.value_initialized initialized)
  · intro address expected value stored initialized head notFloat
    exact .scalar (permutation.stores stored) (permutation.value_initialized initialized)
      (by rw [permutation.value_head,head]; rfl) notFloat
  · intro address value stored head initialized
    exact .unit (permutation.stores stored) (by rw [permutation.value_head,head]; rfl) (permutation.value_initialized initialized)
  · intro address value fields stored head live length _ ih
    exact .tuple (permutation.stores stored) (by rw [permutation.value_head,head]; rfl)
      (by rw [permutation.value_live]; exact live) (by simpa only [permutation.value_fields,List.length_map] using length) ih
  · intro address value fields stored head initialized length _ ih
    exact .array (permutation.stores stored) (by rw [permutation.value_head,head]; rfl)
      (permutation.value_initialized initialized) (by simpa only [permutation.value_fields,List.length_map] using length) ih
  · intro address value variant fields stored head live length _ ih
    exact .constructor (permutation.stores stored) (by rw [permutation.value_head,head]; rfl)
      (by rw [permutation.value_live]; exact live) (by simpa only [permutation.value_fields,List.length_map] using length) ih
  · intro address value id loan mode pattern stored head found live modeEq _ ih
    exact .reference (loan := permutation.loan loan) (permutation.stores stored)
      (by rw [permutation.value_head,head]; rfl) (by rw [permutation.world_loans,found]; rfl) live modeEq ih
  · intro address offset; exact .nil
  · intro address offset first rest _ _ ihFirst ihRest; exact .cons ihFirst ihRest

theorem RegionPermutation.pattern_involutive (permutation : RegionPermutation) (pattern : Kernel.Pattern) :
    (pattern.mapTerms permutation.term).mapTerms permutation.term = pattern := by
  rw [Kernel.Pattern.mapTerms_comp]
  exact pattern.mapTerms_eq_self _ (fun term _ => permutation.term_involutive term)

theorem RegionPermutation.matches_iff (permutation : RegionPermutation) {program : Program} {world : World}
    {address : Address} {pattern : Kernel.Pattern} :
    Kernel.Matches program (permutation.world world) address (pattern.mapTerms permutation.term) ↔
      Kernel.Matches program world address pattern := by
  constructor
  · intro matched
    have original := permutation.matches matched
    rw [permutation.pattern_involutive] at original
    exact original.transport (fun address => (permutation.world_read_twice world address).symm)
      (fun id => (permutation.world_loans_twice world id).symm)
  · exact permutation.matches

theorem RegionPermutation.arm_involutive (permutation : RegionPermutation) (arm : Kernel.Arm) :
    (arm.mapTerms permutation.term).mapTerms permutation.term = arm := by
  cases arm
  simp only [Kernel.Arm.mapTerms,Kernel.Arm.transformTerms,permutation.pattern_involutive]
  congr 1
  exact permutation.code_involutive _

theorem RegionPermutation.arm_pattern (permutation : RegionPermutation) (arm : Kernel.Arm) :
    (arm.mapTerms permutation.term).pattern = arm.pattern.mapTerms permutation.term := by
  cases arm; simp only [Kernel.Arm.mapTerms,Kernel.Arm.transformTerms,Kernel.Arm.pattern]

theorem RegionPermutation.firstArm (permutation : RegionPermutation) {program : Program} {world : World}
    {address : Address} {arms : List Kernel.Arm} {arm : Kernel.Arm} (selected : Kernel.FirstArm program world address arms arm) :
    Kernel.FirstArm program (permutation.world world) address (arms.map (Kernel.Arm.mapTerms permutation.term))
      (arm.mapTerms permutation.term) := by
  obtain ⟨skipped,rest,rfl,matched,earlier⟩ := selected
  refine ⟨skipped.map (Kernel.Arm.mapTerms permutation.term),rest.map (Kernel.Arm.mapTerms permutation.term),
    by simp only [List.map_append,List.map_cons],?_,?_⟩
  · rw [permutation.arm_pattern]; exact permutation.matches matched
  · intro arm member matched
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    rw [permutation.arm_pattern] at matched
    exact earlier original present (permutation.matches_iff.mp matched)

theorem Kernel.FirstArm.transport {program : Language.Program} {before after : World} {address : Address}
    {arms : List Kernel.Arm} {arm : Kernel.Arm} (selected : Kernel.FirstArm program before address arms arm)
    (read : ∀ address, after.read address = before.read address)
    (loans : ∀ id, after.loans.get id = before.loans.get id) : Kernel.FirstArm program after address arms arm := by
  obtain ⟨skipped,rest,equal,matched,earlier⟩ := selected
  exact ⟨skipped,rest,equal,matched.transport read loans,fun arm member matched =>
    earlier arm member (matched.transport (fun address => (read address).symm) (fun id => (loans id).symm))⟩

theorem Typing.PatternCoverage.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {type : Term} {arms : List Kernel.Arm}
    (covered : Typing.PatternCoverage program type arms) (permutation : RegionPermutation) :
    Typing.PatternCoverage program (permutation.term type) (arms.map (Kernel.Arm.mapTerms permutation.term)) := by
  constructor
  · intro world address value typed stored shape initialized
    have worldTyped : Typing.WorldTyped program (permutation.world world) := permutation.worldTyped valid inventory typed
    obtain ⟨arm,selected⟩ := covered.1 (permutation.world world) address (permutation.value value) worldTyped
      (permutation.stores stored) (by rw [permutation.value_type,shape,permutation.term_involutive])
      (permutation.value_initialized initialized)
    exact ⟨arm.mapTerms permutation.term,(permutation.firstArm selected).transport
      (fun address => (permutation.world_read_twice world address).symm)
      (fun id => (permutation.world_loans_twice world id).symm)⟩
  · intro arm member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨world,address,value,typed,stored,shape,initialized,selected⟩ := covered.2 original present
    exact ⟨permutation.world world,address,permutation.value value,permutation.worldTyped valid inventory typed,
      permutation.stores stored,by rw [permutation.value_type,shape],permutation.value_initialized initialized,
      permutation.firstArm selected⟩

end Glorious.Language
