import GloriousLanguage.StorageTyping

/-! Preservation obligations for the actual storage and execution relations.
No result in this module assumes `ResourceAdmission` or the safety conclusion
it proves. The whole-machine preservation/progress proof is still in progress. -/
namespace Glorious.Language

/-- Proof projection, not additional runtime state: nested field writes retain
identity, type, constructor, shell-liveness and arity, but not field contents. -/
def Value.shell (value : Value) : Value := value.withFields (List.replicate value.fields.length none)

theorem Value.replace_cons_shape {before after : Value} {index : Nat} {path : List Nat}
    {replacement : Option Value} (written : before.replace (index :: path) replacement = some after) :
    ∃ field, before.fields[index]? = some field ∧
      ((path = [] ∧ after = before.withFields (before.fields.set index replacement)) ∨
       ∃ child changed, field = some child ∧ child.replace path replacement = some changed ∧
         after = before.withFields (before.fields.set index (some changed))) := by
  unfold Value.replace at written
  cases found : before.fields[index]? with
  | none => simp [found] at written
  | some field =>
      refine ⟨field,rfl,?_⟩
      simp only [found] at written
      dsimp at written
      split at written
      next empty =>
        exact Or.inl ⟨by simpa using empty,(Option.some.inj written).symm⟩
      next =>
        cases field with
        | none => simp at written
        | some child =>
            dsimp at written
            cases replaced : child.replace path replacement with
            | none => simp [replaced] at written
            | some changed =>
                simp only [replaced] at written
                dsimp at written
                exact Or.inr ⟨child,changed,rfl,replaced,(Option.some.inj written).symm⟩

theorem Value.replace_shell {before after : Value} {path : List Nat} {replacement : Option Value}
    (written : before.replace path replacement = some after) (nonempty : path ≠ []) :
    after.shell = before.shell := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons index path =>
      rcases Value.replace_cons_shape written with ⟨_,_,⟨_,rfl⟩ | ⟨_,_,_,_,rfl⟩⟩ <;>
        simp [Value.shell,Value.withFields,Value.owner,Value.type,Value.head,Value.shellLive,Value.fields]

/-- A write cannot change an ancestor's constructor or any sibling subtree.
The excluded case is exactly an observation inside the replaced subtree. -/
theorem Value.replace_atPath_shell {before after : Value} {path observed : List Nat}
    {replacement : Option Value} (written : before.replace path replacement = some after)
    (outside : ¬ ∃ suffix, observed = path ++ suffix) :
    (after.atPath observed).map Value.shell = (before.atPath observed).map Value.shell := by
  induction path generalizing before after observed with
  | nil => exact False.elim (outside ⟨observed,rfl⟩)
  | cons index path ih =>
      cases observed with
      | nil =>
          simpa [Value.atPath] using Value.replace_shell written (by simp)
      | cons other observed =>
          rcases Value.replace_cons_shape written with ⟨field,found,⟨rfl,rfl⟩ | ⟨child,changed,rfl,replaced,rfl⟩⟩
          · have different : index ≠ other := by
              intro same
              subst other
              exact outside ⟨observed,rfl⟩
            simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne different]
          · by_cases same : index = other
            · subst other
              have inBounds : index < before.fields.length := List.getElem?_eq_some_iff.mp found |>.1
              have restOutside : ¬ ∃ suffix, observed = path ++ suffix := by
                rintro ⟨suffix,equal⟩
                exact outside ⟨suffix,by simp [equal]⟩
              change (((before.fields.set index (some changed))[index]?).join >>= fun value => value.atPath observed).map Value.shell =
                ((before.fields[index]?).join >>= fun value => value.atPath observed).map Value.shell
              rw [List.getElem?_set_self inBounds,found]
              exact ih replaced restOutside
            · simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne same]

theorem Value.atPath_append (value : Value) (path suffix : List Nat) :
    value.atPath (path ++ suffix) = value.atPath path >>= fun resident => resident.atPath suffix := by
  induction path generalizing value with
  | nil => rfl
  | cons index path ih =>
      simp only [List.cons_append,Value.atPath]
      cases found : value.fields[index]?.join with
      | none => rfl
      | some child => exact ih child

theorem World.read_append (world : World) (address : Address) (suffix : List Nat) :
    world.read { address with fields := address.fields ++ suffix } =
      world.read address >>= fun value => value.atPath suffix := by
  simp [World.read,World.root,Value.atPath_append,Option.bind_assoc]

theorem World.Stores.prefix {world : World} {ancestor descendant : Address} {value : Value}
    (stored : world.Stores descendant value) (included : ancestor.Prefix descendant) :
    ∃ resident, world.Stores ancestor resident := by
  rcases included with ⟨root,generation,suffix,fields⟩
  have addressEq : descendant = { ancestor with fields := ancestor.fields ++ suffix } := by
    cases ancestor
    cases descendant
    simp_all
  change world.read descendant = some value at stored
  rw [addressEq,World.read_append] at stored
  obtain ⟨resident,found,_⟩ := Option.bind_eq_some_iff.mp stored
  exact ⟨resident,found⟩

theorem World.Vacant.not_stored {world : World} {address : Address}
    (vacant : world.Vacant address) : ¬ ∃ value, world.Stores address value := by
  rcases vacant with ⟨root,selected,⟨fields,empty⟩ | ⟨parent,index,tree,fields,resident,container,found,empty⟩⟩
  · rintro ⟨value,stored⟩
    simp [World.Stores,World.read,selected,empty] at stored
  · rintro ⟨value,stored⟩
    simp [World.Stores,World.read,selected,resident,fields,Value.atPath_append,found,Value.atPath,empty] at stored

theorem World.Located.ancestor_stored {world : World} {ancestor descendant : Address}
    (located : world.Located descendant) (included : ancestor.ProperPrefix descendant) :
    ∃ value, world.Stores ancestor value := by
  rcases located with ⟨value,stored⟩ | ⟨root,selected,⟨fields,_⟩ | ⟨parent,index,tree,fields,resident,container,found,_⟩⟩
  · exact stored.prefix included.1
  · have length := included.2
    simp [fields] at length
  · have parentStored : world.Stores { descendant with fields := parent } container := by
      change (world.root descendant >>= fun root => root.value >>= fun value => value.atPath parent) = some container
      simp [selected,resident,found]
    apply parentStored.prefix
    refine ⟨included.1.1,included.1.2.1,?_⟩
    have ancestorPrefix : ancestor.fields <+: descendant.fields :=
      List.prefix_iff_exists_eq_append.mpr included.1.2.2
    have parentPrefix : parent <+: descendant.fields := by rw [fields]; exact List.prefix_append _ _
    have length : ancestor.fields.length ≤ parent.length := by
      have strict := included.2
      simp only [fields,List.length_append,List.length_singleton] at strict
      omega
    exact List.prefix_iff_exists_eq_append.mp (List.prefix_of_prefix_length_le ancestorPrefix parentPrefix length)

theorem World.Vacant.no_located_descendant {world : World} {ancestor descendant : Address}
    (vacant : world.Vacant ancestor) (located : world.Located descendant) : ¬ ancestor.ProperPrefix descendant :=
  fun included => vacant.not_stored (located.ancestor_stored included)

theorem Table.mem_of_get {α : Type} {table : Table α} {id : Identity} {value : α}
    (found : table.get id = some value) : (id,value) ∈ table := by
  induction table with
  | nil => simp [Table.get] at found
  | cons entry rest ih =>
      rcases entry with ⟨key,resident⟩
      by_cases same : key = id
      · subst key
        have equal : resident = value := by simpa [Table.get] using found
        subst resident
        exact List.mem_cons_self
      · have later : Table.get rest id = some value := by simpa [Table.get,same] using found
        exact List.mem_cons_of_mem _ (ih later)

theorem World.root_found {world : World} {address : Address} {root : Root}
    (selected : world.root address = some root) :
    world.roots.get address.root = some root ∧ root.live = true ∧ root.generation = address.generation := by
  unfold World.root at selected
  cases found : world.roots.get address.root with
  | none => simp [found] at selected
  | some resident =>
      simp only [found] at selected
      dsimp at selected
      split at selected
      next valid =>
        have same := Option.some.inj selected
        subst resident
        exact ⟨rfl,by simpa using valid⟩
      next => contradiction

theorem World.Located.root_iff {world : World} {address : Address} (whole : address.fields = []) :
    world.Located address ↔ ∃ root, world.root address = some root := by
  constructor
  · rintro (⟨value,stored⟩ | ⟨root,selected,_⟩)
    · exact ⟨_,(Option.bind_eq_some_iff.mp stored).choose_spec.1⟩
    · exact ⟨root,selected⟩
  · rintro ⟨root,selected⟩
    cases resident : root.value with
    | none => exact Or.inr ⟨root,selected,Or.inl ⟨whole,resident⟩⟩
    | some value => exact Or.inl ⟨value,by simp [World.Stores,World.read,selected,resident,whole,Value.atPath]⟩

theorem World.Located.child_iff {world : World} {address : Address} {index : Nat} :
    world.Located (address.child index) ↔ ∃ value, world.Stores address value ∧ index < value.fields.length := by
  constructor
  · rintro (⟨value,stored⟩ | ⟨root,selected,⟨whole,_⟩ | ⟨parent,other,tree,fields,resident,container,found,empty⟩⟩)
    · change world.read { address with fields := address.fields ++ [index] } = some value at stored
      rw [World.read_append] at stored
      obtain ⟨container,parentStored,childStored⟩ := Option.bind_eq_some_iff.mp stored
      have field : container.fields[index]? = some (some value) :=
        Option.join_eq_some_iff.mp (by simpa [Value.atPath] using childStored)
      exact ⟨container,parentStored,(List.getElem?_eq_some_iff.mp field).1⟩
    · simp [Address.child] at whole
    · change address.fields ++ [index] = parent ++ [other] at fields
      obtain ⟨parentEq,indexEq⟩ := List.append_inj' fields rfl
      subst parent
      have same : index = other := List.singleton_inj.mp indexEq
      subst other
      refine ⟨container,?_,(List.getElem?_eq_some_iff.mp empty).1⟩
      have selectedParent : world.root address = some root := selected
      simp [World.Stores,World.read,selectedParent,resident,found]
  · rintro ⟨container,stored,bound⟩
    obtain ⟨field,found⟩ : ∃ field, container.fields[index]? = some field :=
      ⟨container.fields[index],List.getElem?_eq_getElem bound⟩
    cases field with
    | some value =>
        apply Or.inl
        refine ⟨value,?_⟩
        change world.read { address with fields := address.fields ++ [index] } = some value
        rw [World.read_append,stored]
        simp [Value.atPath,found]
    | none =>
        obtain ⟨root,selected,rest⟩ := Option.bind_eq_some_iff.mp stored
        obtain ⟨tree,resident,path⟩ := Option.bind_eq_some_iff.mp rest
        exact Or.inr ⟨root,selected,Or.inr ⟨address.fields,index,tree,rfl,resident,container,path,found⟩⟩

/-- Even a nested write changes only the resident tree, never the declared
storage location, layout, generation, region or liveness of its root. -/
theorem World.write_value_update {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) :
    ∃ root replacement, before.roots.get address.root = some root ∧
      after = { before with roots := before.roots.set address.root { root with value := replacement } } := by
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
      have found := (World.root_found selected).1
      simp only [selected] at written
      dsimp at written
      split at written
      next => exact ⟨root,value,found,(Option.some.inj written).symm⟩
      next =>
        cases resident : root.value with
        | none => simp [resident] at written
        | some tree =>
            simp only [resident] at written
            dsimp at written
            cases replaced : tree.replace address.fields value with
            | none => simp [replaced] at written
            | some changed =>
                simp only [replaced] at written
                dsimp at written
                exact ⟨root,some changed,found,(Option.some.inj written).symm⟩

def Root.location (root : Root) : Root := { root with value := none }

theorem RawPointer.Origin.transport {pointer : RawPointer} {before after : World}
    (origin : pointer.Origin before)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location) :
    pointer.Origin after := by
  intro id allocation
  obtain ⟨root,found,address,offset⟩ := origin id allocation
  have location := locations id
  rw [found] at location
  obtain ⟨changed,selected,same⟩ := Option.map_eq_some_iff.mp location
  have base := congrArg Root.base same
  have layout := congrArg Root.layout same
  change changed.base = root.base at base
  change changed.layout = root.layout at layout
  exact ⟨changed,selected,by simpa only [Root.location] using address.trans (congrArg (· + pointer.offset) base.symm),
    by simpa only [layout] using offset⟩

theorem World.root_transport {before after : World} {address : Address} {root : Root}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (selected : before.root address = some root) :
    ∃ resident, after.root address = some resident ∧ resident.location = root.location := by
  obtain ⟨found,live,generation⟩ := World.root_found selected
  have location := locations address.root
  rw [found] at location
  cases changed : after.roots.get address.root with
  | none => simp [changed] at location
  | some resident =>
      rw [changed] at location
      have same := Option.some.inj location
      have residentGeneration : resident.generation = root.generation := by simpa [Root.location] using congrArg Root.generation same
      have residentLive : resident.live = root.live := by simpa [Root.location] using congrArg Root.live same
      exact ⟨resident,by simp [World.root,changed,residentLive,live,residentGeneration,generation],same⟩

theorem World.write_locations {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  rcases World.write_value_update written with ⟨root,replacement,found,rfl⟩
  by_cases same : id = address.root
  · subst id
    rw [Table.get_set,found]
    rfl
  · rw [Table.get_set_other _ _ _ _ same]

theorem World.write_loans {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : after.loans = before.loans := by
  rcases World.write_value_update written with ⟨_,_,_,rfl⟩
  rfl

theorem Address.Prefix.child {ancestor descendant : Address} (included : ancestor.Prefix descendant) (index : Nat) :
    ancestor.ProperPrefix (descendant.child index) := by
  rcases included with ⟨root,generation,suffix,fields⟩
  refine ⟨⟨root,generation,suffix ++ [index],?_⟩,?_⟩
  · simp [Address.child,fields,List.append_assoc]
  · simp [Address.child,fields]

theorem Address.Prefix.refl (address : Address) : address.Prefix address := ⟨rfl,rfl,[],by simp⟩

theorem Address.Prefix.trans {first middle last : Address}
    (left : first.Prefix middle) (right : middle.Prefix last) : first.Prefix last := by
  rcases left with ⟨root,generation,suffix,fields⟩
  rcases right with ⟨nextRoot,nextGeneration,nextSuffix,nextFields⟩
  exact ⟨root.trans nextRoot,generation.trans nextGeneration,suffix ++ nextSuffix,
    by simp [nextFields,fields,List.append_assoc]⟩

theorem Address.Prefix.length_le {first last : Address} (included : first.Prefix last) :
    first.fields.length ≤ last.fields.length := by
  rcases included with ⟨_,_,suffix,fields⟩
  simp [fields]

theorem Address.Prefix.overlaps {first last : Address} (included : first.Prefix last) : first.Overlaps last :=
  ⟨included.1,included.2.1,Or.inr included.2.2⟩

theorem AncestorLoan.containment {world : World} {ancestor descendant : Identity} {first last : Loan}
    (parents : world.LoanParents) (ancestry : AncestorLoan world ancestor descendant)
    (foundFirst : world.loans.get ancestor = some first) (foundLast : world.loans.get descendant = some last) :
    first.referent.Prefix last.referent := by
  induction ancestry generalizing last with
  | refl =>
      have same := Option.some.inj (foundFirst.symm.trans foundLast)
      subst last
      exact .refl _
  | @parent parent child loan found selected _ ih =>
      have same := Option.some.inj (found.symm.trans foundLast)
      subst last
      obtain ⟨middle,located,_,included,_,_⟩ := parents child loan parent found selected
      exact (ih located).trans included

theorem AncestorLoan.identity_le {world : World} {ancestor descendant : Identity}
    (parents : world.LoanParents) (ancestry : AncestorLoan world ancestor descendant) : ancestor ≤ descendant := by
  induction ancestry with
  | refl => exact Nat.le_refl _
  | parent found selected _ ih =>
      obtain ⟨_,_,bound,_⟩ := parents _ _ _ found selected
      exact Nat.le_trans ih (Nat.le_of_lt bound)

theorem AncestorLoan.antisymm {world : World} {left right : Identity}
    (parents : world.LoanParents) (forward : AncestorLoan world left right) (backward : AncestorLoan world right left) :
    left = right := Nat.le_antisymm (forward.identity_le parents) (backward.identity_le parents)

theorem Permitted.parentLoan {world : World} {authority : Authority} {requested : Access} {address : Address} {id : Identity}
    (permitted : Permitted world authority requested address) (selected : authority.parentLoan = some id) :
    ∃ loan, world.loans.get id = some loan ∧ loan.live = true ∧ loan.referent.Prefix address ∧
      (requested ≠ .shared → loan.mode = .unique) := by
  induction authority with
  | owner => cases selected
  | loan actual =>
      have equal : actual = id := Option.some.inj selected
      subst actual
      obtain ⟨_,loan,found,live,root,generation,path,mode,_⟩ := permitted
      exact ⟨loan,found,live,⟨root,generation,path⟩,mode⟩
  | shared backing ih => exact ih permitted.2.2 selected

/-- A consumption authorized by the actual loan graph cannot remove a proper
ancestor of a live loan. This derives the source framing condition rather than
assuming that the after-world is safe. -/
theorem Permitted.owned_no_loan_descendant {world : World} {authority : Authority} {address : Address}
    (parents : world.LoanParents) (permitted : Permitted world authority .owned address)
    {id : Identity} {loan : Loan} (found : world.loans.get id = some loan) (live : loan.live = true) :
    ¬ address.ProperPrefix loan.referent := by
  rintro ⟨included,longer⟩
  cases authority with
  | owner => exact permitted.2 id loan found live included.overlaps (Or.inl (by decide))
  | shared backing => cases permitted.2.1
  | loan activeId =>
      obtain ⟨_,active,selected,_,root,generation,path,_,conflicts⟩ := permitted
      have activeContains : active.referent.Prefix address := ⟨root,generation,path⟩
      by_cases same : id = activeId
      · subst id
        have equal := Option.some.inj (selected.symm.trans found)
        subst loan
        have bound := activeContains.length_le
        omega
      · have ancestor := conflicts id loan found live same included.overlaps (Or.inl (by decide))
        have bound := ((ancestor.containment parents found selected).trans activeContains).length_le
        omega

theorem Borrows.loanParents {program : Program} {before after : World} {authority mode region referent destination}
    (valid : before.WellFormed) (borrowed : Borrows program before authority mode region referent destination after) :
    after.LoanParents := by
  cases borrowed with
  | borrow _ _ _ _ _ permitted _ _ parentEq _ =>
      intro id loan parent found selected
      by_cases fresh : id = before.nextLoan
      · subst id
        simp only [Table.get_set] at found
        cases found
        obtain ⟨ancestor,parentFound,parentLive,included,parentMode⟩ :=
          permitted.parentLoan (parentEq.symm.trans selected)
        have bound := World.loanBounds valid parentFound
        refine ⟨ancestor,?_,bound,included,?_,fun _ => parentLive⟩
        · simpa only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)] using parentFound
        · intro unique
          change mode = .unique at unique
          exact parentMode (by simp [unique])
      · have oldFound : before.loans.get id = some loan := by
          simpa only [Table.get_set_other _ _ _ _ fresh] using found
        obtain ⟨ancestor,parentFound,bound,included,parentMode,parentLive⟩ := World.loanParents valid id loan parent oldFound selected
        refine ⟨ancestor,?_,bound,included,parentMode,parentLive⟩
        simpa only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid parentFound))] using parentFound

theorem EndsLoan.loanParents {before after : World} {id : Identity}
    (valid : before.WellFormed) (ended : EndsLoan before id after) : after.LoanParents := by
  cases ended with
  | restored selected _ _ _ children =>
      intro child loan parent found link
      by_cases changed : child = id
      · subst child
        simp only [Table.get_set] at found
        cases found
        obtain ⟨ancestor,parentFound,bound,included,parentMode,_⟩ := World.loanParents valid _ _ _ selected link
        refine ⟨ancestor,?_,bound,included,parentMode,?_⟩
        · simpa only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)] using parentFound
        · intro impossible
          cases impossible
      · have oldFound : before.loans.get child = some loan := by
          simpa only [Table.get_set_other _ _ _ _ changed] using found
        obtain ⟨ancestor,parentFound,bound,included,parentMode,parentLive⟩ := World.loanParents valid _ _ _ oldFound link
        by_cases parentChanged : parent = id
        · subst parent
          have same := Option.some.inj (selected.symm.trans parentFound)
          subst ancestor
          refine ⟨_,Table.get_set _ _ _,bound,included,parentMode,?_⟩
          have identity := World.loanIdentity valid oldFound
          have dead := children loan (by simpa [← identity] using oldFound) link
          intro live
          simp [live] at dead
        · exact ⟨ancestor,by simpa only [Table.get_set_other _ _ _ _ parentChanged] using parentFound,
            bound,included,parentMode,parentLive⟩

theorem EndsLoan.liveLoanLocations {before after : World} {id : Identity}
    (locations : before.LiveLoanLocations) (ended : EndsLoan before id after) : after.LiveLoanLocations := by
  cases ended with
  | restored _ _ _ _ _ =>
      intro child loan found live
      by_cases changed : child = id
      · subst child
        simp only [Table.get_set] at found
        cases found
        cases live
      · have oldFound : before.loans.get child = some loan := by
          simpa only [Table.get_set_other _ _ _ _ changed] using found
        exact locations child loan oldFound live

theorem World.write_read_shell {before after : World} {address observed : Address} {value : Option Value}
    (written : before.write address value = some after) (outside : ¬ address.Prefix observed) :
    (after.read observed).map Value.shell = (before.read observed).map Value.shell := by
  have update := World.write_value_update written
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
      obtain ⟨found,live,generation⟩ := World.root_found selected
      simp only [selected] at written
      dsimp at written
      by_cases sameRoot : observed.root = address.root
      · by_cases sameGeneration : observed.generation = address.generation
        · have pathOutside : ¬ ∃ suffix, observed.fields = address.fields ++ suffix :=
            fun included => outside ⟨sameRoot.symm,sameGeneration.symm,included⟩
          split at written
          next empty =>
            have fields : address.fields = [] := by simpa using empty
            exact False.elim (pathOutside ⟨observed.fields,by simp [fields]⟩)
          next =>
            cases resident : root.value with
            | none => simp [resident] at written
            | some tree =>
                simp only [resident] at written
                dsimp at written
                cases replaced : tree.replace address.fields value with
                | none => simp [replaced] at written
                | some changed =>
                    simp only [replaced] at written
                    dsimp at written
                    cases (Option.some.inj written).symm
                    have observedGeneration : root.generation = observed.generation := generation.trans sameGeneration.symm
                    have unchanged := Value.replace_atPath_shell replaced pathOutside
                    simpa [World.read,World.root,Table.get_set,sameRoot,found,live,observedGeneration,resident]
                      using unchanged
        · rcases update with ⟨changedRoot,_,changedFound,equal⟩
          have same := Option.some.inj (changedFound.symm.trans found)
          subst changedRoot
          subst after
          have different : root.generation ≠ observed.generation := by omega
          simp [World.read,World.root,sameRoot,Table.get_set,found,live,different]
      · rcases update with ⟨_,_,_,equal⟩
        subst after
        simp [World.read,World.root,Table.get_set_other _ _ _ _ sameRoot]

theorem World.Located.transport {before after : World} {mutation address : Address}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (shells : ∀ observed, ¬ mutation.Prefix observed →
      (after.read observed).map Value.shell = (before.read observed).map Value.shell)
    (outside : ¬ mutation.ProperPrefix address) (located : before.Located address) : after.Located address := by
  rcases address with ⟨id,generation,fields⟩
  rcases List.eq_nil_or_concat fields with whole | ⟨parent,index,whole⟩
  · subst fields
    obtain ⟨root,selected⟩ := (World.Located.root_iff rfl).mp located
    obtain ⟨resident,found,_⟩ := World.root_transport locations selected
    exact (World.Located.root_iff rfl).mpr ⟨resident,found⟩
  · simp only [List.concat_eq_append] at whole
    subst fields
    change before.Located ((⟨id,generation,parent⟩ : Address).child index) at located
    obtain ⟨container,stored,bound⟩ := World.Located.child_iff.mp located
    have parentOutside : ¬ mutation.Prefix ⟨id,generation,parent⟩ := fun included => outside (included.child index)
    have framed := shells ⟨id,generation,parent⟩ parentOutside
    rw [stored] at framed
    cases found : after.read ⟨id,generation,parent⟩ with
    | none => simp [found] at framed
    | some resident =>
        rw [found] at framed
        have same := Option.some.inj framed
        have arity : resident.fields.length = container.fields.length := by
          simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) same
        exact World.Located.child_iff.mpr ⟨resident,found,by omega⟩

theorem World.write_located {before after : World} {mutation address : Address} {value : Option Value}
    (written : before.write mutation value = some after) (outside : ¬ mutation.ProperPrefix address)
    (located : before.Located address) : after.Located address :=
  located.transport (World.write_locations written) (fun _ => World.write_read_shell written) outside

theorem Borrows.liveLoanLocations {program : Program} {before after : World} {authority mode region referent destination}
    (locations : before.LiveLoanLocations) (borrowed : Borrows program before authority mode region referent destination after) :
    after.LiveLoanLocations := by
  cases borrowed with
  | borrow stored _ _ _ _ _ vacant _ _ written =>
      intro id loan found live
      by_cases fresh : id = before.nextLoan
      · subst id
        simp only [Table.get_set] at found
        cases found
        have located : before.Located referent := Or.inl ⟨_,stored⟩
        have result := World.write_located written (vacant.no_located_descendant located) located
        exact result
      · have oldFound : before.loans.get id = some loan := by
          simpa only [Table.get_set_other _ _ _ _ fresh] using found
        have located := locations id loan oldFound live
        have result := World.write_located written (vacant.no_located_descendant located) located
        exact result

theorem Transfers.locations {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_locations install id).trans (World.write_locations clear id)

theorem Transfers.loans {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) : after.loans = before.loans := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_loans install).trans (World.write_loans clear)

theorem Transfers.loanParents {program : Program} {before after : World} {authority source destination}
    (parents : before.LoanParents) (transfer : Transfers program before authority source destination after) :
    after.LoanParents := by simpa [World.LoanParents,transfer.loans] using parents

theorem Transfers.liveLoanLocations {program : Program} {before after : World} {authority source destination}
    (valid : before.WellFormed) (transfer : Transfers program before authority source destination after) :
    after.LiveLoanLocations := by
  have loans := transfer.loans
  cases transfer with
  | move _ _ permission vacant _ _ clear install =>
      intro id loan found live
      have oldFound : before.loans.get id = some loan := by simpa [loans] using found
      have located := World.liveLoanLocations valid id loan oldFound live
      have sourceOutside := permission.owned_no_loan_descendant (World.loanParents valid) oldFound live
      have destinationOutside := vacant.no_located_descendant located
      exact World.write_located install destinationOutside (World.write_located clear sourceOutside located)

theorem Transfers.destination_vacant {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) : before.Vacant destination := by
  cases transfer
  assumption

theorem Transfers.destination_type {program : Program} {before after : World} {authority source destination value}
    (transfer : Transfers program before authority source destination after) (stored : before.Stores source value) :
    AddressType program before destination value.type := by
  cases transfer with
  | move found _ _ _ _ typed _ _ =>
      have same := Option.some.inj (stored.symm.trans found)
      subst same
      exact typed

theorem Copies.destination_type {program : Program} {before after : World} {authority source destination value}
    (copy : Copies program before authority source destination after) (stored : before.Stores source value) :
    AddressType program before destination value.type := by
  cases copy with
  | copy found _ _ _ typed _ _ =>
      have same := Option.some.inj (stored.symm.trans found)
      subst same
      exact typed

theorem NewValue.destination_type {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : AddressType program before destination type := by
  cases constructed
  assumption

theorem AddressType.root_iff {program : Program} {world : World} {address : Address} {type : Term}
    (whole : address.fields = []) :
    AddressType program world address type ↔ ∃ root, world.root address = some root ∧ root.type = type := by
  constructor
  · rintro ⟨offset,typed⟩
    cases typed with
    | root found live => exact ⟨_,by simp [World.root,found,live],rfl⟩
    | child _ _ => simp [Address.child] at whole
  · rintro ⟨root,selected,rfl⟩
    obtain ⟨found,live,generation⟩ := World.root_found selected
    rcases address with ⟨id,epoch,fields⟩
    change fields = [] at whole
    subst fields
    change root.generation = epoch at generation
    subst epoch
    exact ⟨0,.root found live⟩

theorem AddressType.root_transport {program : Program} {before after : World} {address : Address} {type : Term}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (whole : address.fields = []) (typed : AddressType program before address type) :
    AddressType program after address type := by
  rcases (AddressType.root_iff whole).mp typed with ⟨root,selected,typeEq⟩
  obtain ⟨resident,found,same⟩ := World.root_transport locations selected
  have residentType : resident.type = root.type := by simpa [Root.location] using congrArg Root.type same
  exact (AddressType.root_iff whole).mpr ⟨resident,found,residentType.trans typeEq⟩

theorem Transfers.root_types {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) {address : Address} {type : Term}
    (whole : address.fields = []) : AddressType program before address type ↔ AddressType program after address type := by
  constructor
  · exact AddressType.root_transport transfer.locations whole
  · exact AddressType.root_transport (fun id => (transfer.locations id).symm) whole

theorem FieldOffset.transport {program : Program} {before after : World}
    {address : Address} {container type : Term} {index offset : Nat}
    (shells : (after.read address).map Value.shell = (before.read address).map Value.shell)
    (field : FieldOffset program before address container index type offset) :
    FieldOffset program after address container index type offset := by
  cases field with
  | tuple selected layouts layout offset => exact .tuple selected layouts layout offset
  | bindings selected layouts layout offset => exact .bindings selected layouts layout offset
  | callable captures selected layouts layout offset => exact .callable captures selected layouts layout offset
  | array nonnegative bound layout => exact .array nonnegative bound layout
  | nominal constructor id instantiated substituted selected layout stored head offset =>
      change before.read address = some _ at stored
      rw [stored] at shells
      cases found : after.read address with
      | none => simp [found] at shells
      | some resident =>
          rw [found] at shells
          have same := Option.some.inj shells
          have sameHead := congrArg Value.head same
          simp only [Value.shell,Value.withFields,Value.head] at sameHead
          exact .nominal constructor id instantiated substituted selected layout found (sameHead.trans head) offset

/-- The shared address/layout derivation survives a write except beneath a
replaced proper ancestor. The address being written may itself become vacant. -/
theorem AddressOffset.transport {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {offset : Nat}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (shells : ∀ observed, ¬ mutation.Prefix observed →
      (after.read observed).map Value.shell = (before.read observed).map Value.shell)
    (outside : ¬ mutation.ProperPrefix address) (typed : AddressOffset program before address type offset) :
    AddressOffset program after address type offset := by
  induction typed with
  | @root id root found live =>
      have location := locations id
      rw [found] at location
      cases changed : after.roots.get id with
      | none => simp [changed] at location
      | some resident =>
          rw [changed] at location
          have same := Option.some.inj location
          have residentType : resident.type = root.type := by simpa [Root.location] using congrArg Root.type same
          have residentGeneration : resident.generation = root.generation := by simpa [Root.location] using congrArg Root.generation same
          have residentLive : resident.live = true := by simpa [Root.location,live] using congrArg Root.live same
          simpa only [residentType,residentGeneration] using (AddressOffset.root (program := program) changed residentLive)
  | @child parent container parentOffset index type childOffset _ field ih =>
      have parentOutside : ¬ mutation.Prefix parent := fun included => outside (included.child index)
      exact .child (ih (fun included => parentOutside included.1)) (field.transport (shells parent parentOutside))

theorem World.write_address_offsets {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {offset : Nat} {value : Option Value}
    (written : before.write mutation value = some after) (outside : ¬ mutation.ProperPrefix address) :
    AddressOffset program before address type offset ↔ AddressOffset program after address type offset := by
  constructor
  · exact AddressOffset.transport (World.write_locations written) (fun _ => World.write_read_shell written) outside
  · exact AddressOffset.transport (fun id => (World.write_locations written id).symm)
      (fun _ separate => (World.write_read_shell written separate).symm) outside

theorem World.write_address_types {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {value : Option Value}
    (written : before.write mutation value = some after) (outside : ¬ mutation.ProperPrefix address) :
    AddressType program before address type ↔ AddressType program after address type := by
  exact exists_congr (fun _ => World.write_address_offsets written outside)

theorem Transfers.address_types {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) {address : Address} {type : Term}
    (sourceOutside : ¬ source.ProperPrefix address) (destinationOutside : ¬ destination.ProperPrefix address) :
    AddressType program before address type ↔ AddressType program after address type := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_address_types clear sourceOutside).trans (World.write_address_types install destinationOutside)

/-- A retained reference remains typed across a transfer outside its proper
ancestors. Deriving that side condition for every live loan is a separate
world-invariant obligation; initialization and loan ending remain separate. -/
theorem Transfers.reference_typed {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id loan live}
    (transfer : Transfers program.declarations before authority source destination after)
    (found : before.loans.get id = some loan)
    (sourceOutside : ¬ source.ProperPrefix loan.referent) (destinationOutside : ¬ destination.ProperPrefix loan.referent)
    (typed : Typing.ValueTyped program before
      (.resident owner (.reference mode region type) (.reference id) live [])) :
    Typing.ValueTyped program after (.resident owner (.reference mode region type) (.reference id) live []) := by
  cases typed with
  | aggregate head _ =>
      rcases head with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩ <;> cases impossible
  | reference selected active modeEq regionEq located =>
      have same := Option.some.inj (found.symm.trans selected)
      subst same
      exact .reference (by simpa [transfer.loans] using found) active modeEq regionEq
        ((transfer.address_types sourceOutside destinationOutside).mp located)

theorem Transfers.reference_root_typed {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id loan live}
    (transfer : Transfers program.declarations before authority source destination after)
    (found : before.loans.get id = some loan) (whole : loan.referent.fields = [])
    (typed : Typing.ValueTyped program before
      (.resident owner (.reference mode region type) (.reference id) live [])) :
    Typing.ValueTyped program after (.resident owner (.reference mode region type) (.reference id) live []) := by
  apply transfer.reference_typed found ?_ ?_ typed <;>
    rintro ⟨_,length⟩ <;> simp [whole] at length

/-- No framing condition and no typed post-state are assumed: both forbidden
ancestor cases follow from the pre-state's actual live-loan invariant. -/
theorem Transfers.reference_preserved {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id live}
    (valid : before.WellFormed) (transfer : Transfers program.declarations before authority source destination after)
    (typed : Typing.ValueTyped program before
      (.resident owner (.reference mode region type) (.reference id) live [])) :
    Typing.ValueTyped program after (.resident owner (.reference mode region type) (.reference id) live []) := by
  cases typed with
  | aggregate head _ =>
      rcases head with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩ <;> cases impossible
  | reference selected active modeEq regionEq located =>
      have sourceOutside := transfer.permission.owned_no_loan_descendant (World.loanParents valid) selected active
      have destinationOutside := transfer.destination_vacant.no_located_descendant
        (World.liveLoanLocations valid _ _ selected active)
      exact .reference (by simpa [transfer.loans] using selected) active modeEq regionEq
        ((transfer.address_types sourceOutside destinationOutside).mp located)

theorem Transfers.availability {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) : after.availability = before.availability := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      rcases World.write_value_update clear with ⟨_,_,_,middle⟩
      rcases World.write_value_update install with ⟨_,_,_,finish⟩
      simp [finish,middle]

theorem Typing.ValueTyped.transport {program : Kernel.Program} {before after : World} {value : Value}
    (typed : Typing.ValueTyped program before value)
    (references : ∀ id loan, before.loans.get id = some loan → loan.live = true →
      after.loans.get id = some loan ∧ ∀ type, AddressType program.declarations before loan.referent type →
        AddressType program.declarations after loan.referent type)
    (proofs : after.availability = before.availability)
    (pointers : ∀ pointer : RawPointer, pointer.Origin before → pointer.Origin after) :
    Typing.ValueTyped program after value := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => Typing.ValueTyped program after value)
    (motive_2 := fun fields types _ => Typing.FieldsTyped program after fields types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · exact fun {_ _} => .unit
  · exact fun {_ _ _} checked => .scalar checked
  · exact fun {_ _ _ _ _ _} head _ fields => .aggregate head fields
  · intro owner mode region type id loan live found active modeEq regionEq located
    obtain ⟨selected,types⟩ := references id loan found active
    exact .reference selected active modeEq regionEq (types type located)
  · exact fun {_ _ _ _ _} bound origin => .pointer bound (pointers _ origin)
  · exact fun {_ _ _ _ _ _} selected _ fields => .callable selected fields
  · exact fun {_ _ _ _ _ _} selected => .operation selected
  · exact fun {_ _ _ _ _} => .label
  · exact fun {_ _ _ _} type => .continuation type
  · intro owner brand region id live available found brandEq idEq regionEq
    exact .available (by simpa [proofs] using found) brandEq idEq regionEq
  · exact fun {_ _ _ _ _ _ _} _ brand region length distinct fields => .bindings fields brand region length distinct
  · exact .nil
  · exact fun {_ _ _} _ fields => .hole fields
  · exact fun {_ _ _ _} _ type _ value fields => .resident value type fields

theorem Typing.ValueTyped.transfer {program : Kernel.Program} {before after : World}
    {authority source destination value}
    (valid : before.WellFormed) (transfer : Transfers program.declarations before authority source destination after)
    (typed : Typing.ValueTyped program before value) : Typing.ValueTyped program after value := by
  apply typed.transport ?_ transfer.availability (fun _ origin => origin.transport transfer.locations)
  intro id loan found active
  have sourceOutside := transfer.permission.owned_no_loan_descendant (World.loanParents valid) found active
  have destinationOutside := transfer.destination_vacant.no_located_descendant
    (World.liveLoanLocations valid _ _ found active)
  exact ⟨by simpa [transfer.loans] using found,
    fun _ located => (transfer.address_types sourceOutside destinationOutside).mp located⟩

theorem Value.replace_cons {before child changed : Value} {index : Nat} {path : List Nat}
    {replacement : Option Value} (found : before.fields[index]? = some (some child))
    (written : child.replace path replacement = some changed) :
    before.replace (index :: path) replacement = some (before.withFields (before.fields.set index (some changed))) := by
  cases path with
  | nil =>
      have same : replacement = some changed := written
      simp [Value.replace,found,same]
  | cons next rest =>
      simp only [Value.replace,found,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte]
      change child.replace (next :: rest) replacement >>= _ = _
      rw [written]
      rfl

theorem Value.replace_append_shape {before after : Value} {path suffix : List Nat} {replacement : Option Value}
    (written : before.replace (path ++ suffix) replacement = some after) (nonempty : suffix ≠ []) :
    ∃ parent changed, before.atPath path = some parent ∧ parent.replace suffix replacement = some changed ∧
      before.replace path (some changed) = some after := by
  induction path generalizing before after with
  | nil => exact ⟨before,after,rfl,written,rfl⟩
  | cons index path ih =>
      rcases Value.replace_cons_shape written with ⟨_,found,⟨empty,_⟩ | ⟨child,changed,rfl,nested,rfl⟩⟩
      · exact False.elim (nonempty (List.append_eq_nil_iff.mp empty).2)
      · obtain ⟨parent,replaced,located,rewrite,outer⟩ := ih nested
        exact ⟨parent,replaced,by simp [Value.atPath,found,located],rewrite,Value.replace_cons found outer⟩

theorem World.write_child_shape {before after : World} {address : Address} {index : Nat}
    {replacement : Option Value} (written : before.write (address.child index) replacement = some after) :
    ∃ parent slot, before.Stores address parent ∧ parent.fields[index]? = some slot ∧
      before.write address (some (parent.withFields (parent.fields.set index replacement))) = some after := by
  unfold World.write at written
  cases selected : before.root (address.child index) with
  | none => simp [selected] at written
  | some root =>
      have rootEq : before.root address = some root := selected
      have nonempty : (address.child index).fields.isEmpty = false := by simp [Address.child]
      simp only [selected,nonempty,Bool.false_eq_true,↓reduceIte] at written
      dsimp at written
      cases resident : root.value with
      | none => simp [resident] at written
      | some whole =>
          simp only [resident] at written
          dsimp at written
          cases replaced : whole.replace (address.fields ++ [index]) replacement with
          | none => simp [Address.child,replaced] at written
          | some changed =>
              have result : after = { before with roots := before.roots.set address.root { root with value := some changed } } := by
                simpa [Address.child,replaced] using written.symm
              obtain ⟨parent,newParent,located,rewritten,outer⟩ := Value.replace_append_shape replaced (by simp)
              obtain ⟨slot,found,_⟩ := Value.replace_cons_shape rewritten
              have newParentEq : newParent = parent.withFields (parent.fields.set index replacement) := by
                simpa [Value.replace,found] using rewritten.symm
              refine ⟨parent,slot,?_,found,?_⟩
              · simp [World.Stores,World.read,rootEq,resident,located]
              · rw [result]
                simp only [World.write,rootEq]
                dsimp
                split
                next emptyPath =>
                  have pathEq : address.fields = [] := List.isEmpty_iff.mp emptyPath
                  have changedEq : changed = newParent := by simpa [pathEq,Value.replace] using outer.symm
                  simp [changedEq,newParentEq]
                next => simp [resident,← newParentEq,outer]

theorem ResidentAt.iff_atPath {value resident : Value} {path : List Nat} :
    ResidentAt value path resident ↔ value.atPath path = some resident := by
  constructor
  · intro inside
    induction inside with
    | root => rfl
    | field found _ ih => simp [Value.atPath,found,ih]
  · induction path generalizing value with
    | nil => intro same; cases Option.some.inj same; exact .root
    | cons index path ih =>
        intro found
        obtain ⟨child,selected,nested⟩ := Option.bind_eq_some_iff.mp found
        have slot : value.fields[index]? = some (some child) := by
          cases field : value.fields[index]? <;> simp_all
        exact .field slot (ih nested)

theorem World.resident_iff_stores {world : World} {address : Address} {value : Value} :
    world.Resident address value ↔ world.Stores address value := by
  constructor
  · rintro ⟨root,whole,found,live,generation,resident,inside⟩
    have selected : world.root address = some root := by simp [World.root,found,live,generation]
    simp [World.Stores,World.read,selected,resident,ResidentAt.iff_atPath.mp inside]
  · intro stored
    obtain ⟨root,selected,read⟩ := Option.bind_eq_some_iff.mp stored
    obtain ⟨whole,resident,inside⟩ := Option.bind_eq_some_iff.mp read
    have found := World.root_found selected
    exact ⟨root,whole,found.1,found.2.1,found.2.2.symm,resident,ResidentAt.iff_atPath.mpr inside⟩

theorem World.stores_typed {program : Kernel.Program} {world typingWorld : World} {address : Address} {value : Value}
    (roots : ∀ id root resident, world.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type)
    (stored : world.Stores address value) : Typing.ValueTyped program typingWorld value := by
  obtain ⟨root,whole,found,live,_,resident,inside⟩ := World.resident_iff_stores.mpr stored
  exact (roots _ _ _ found live resident).1.resident inside

theorem World.stores_child {world : World} {address : Address} {index : Nat} {value : Value}
    (stored : world.Stores (address.child index) value) :
    ∃ parent, world.Stores address parent ∧ parent.fields[index]? = some (some value) := by
  change world.read { address with fields := address.fields ++ [index] } = some value at stored
  rw [World.read_append] at stored
  obtain ⟨parent,found,child⟩ := Option.bind_eq_some_iff.mp stored
  refine ⟨parent,found,?_⟩
  cases selected : parent.fields[index]? <;> simp_all [Value.atPath]

theorem AddressOffset.stored_type {program : Kernel.Program} {world typingWorld : World}
    {address : Address} {type : Term} {offset : Nat} {value : Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (roots : ∀ id root resident, world.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type)
    (located : AddressOffset program.declarations world address type offset)
    (stored : world.Stores address value) : value.type = type := by
  induction located generalizing value with
  | root found live =>
      exact (roots _ _ _ found live (by simpa [World.Stores,World.read,World.root,found,live,Value.atPath] using stored)).2
  | child _ field ih =>
      obtain ⟨parent,parentStored,selected⟩ := World.stores_child stored
      have parentType := ih parentStored
      have typed := World.stores_typed roots parentStored
      obtain ⟨types,fields,atType,_⟩ := typed.field_model valid inventory parentStored (parentType ▸ field)
      exact Option.some.inj ((fields.get selected).2.symm.trans atType)

theorem World.write_typed_roots {program : Kernel.Program} {before after typingWorld : World}
    {address : Address} {type : Term} {offset : Nat} {replacement : Option Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (roots : ∀ id root resident, before.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type)
    (located : AddressOffset program.declarations before address type offset)
    (written : before.write address replacement = some after)
    (checked : ∀ value, replacement = some value → Typing.ValueTyped program typingWorld value ∧ value.type = type) :
    ∀ id root resident, after.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type := by
  induction located generalizing after replacement with
  | @root rootId original found live =>
      have selected : before.root ⟨rootId,original.generation,[]⟩ = some original := by
        simp [World.root,found,live]
      have result : after = { before with roots := before.roots.set rootId { original with value := replacement } } := by
        simpa [World.write,selected] using written.symm
      subst after
      intro id root resident present active contents
      by_cases same : rootId = id
      · subst id
        have rootEq : root = { original with value := replacement } := by simpa [Table.get_set] using present.symm
        subst root
        exact checked resident contents
      · exact roots id root resident (by simpa [Table.get_set_other,Ne.symm same] using present) active contents
  | child parent field ih =>
      obtain ⟨container,slot,stored,_,outer⟩ := World.write_child_shape written
      have typeEq := parent.stored_type valid inventory roots stored
      have typed := World.stores_typed roots stored
      apply ih outer
      intro value equal
      cases Option.some.inj equal
      exact ⟨typed.replace_field valid inventory stored (typeEq ▸ field) checked,typeEq⟩

theorem Typing.ValueTyped.clear_path {program : Kernel.Program} {world : World} {before after : Value}
    {path : List Nat} (typed : Typing.ValueTyped program world before)
    (written : before.replace path none = some after) : Typing.ValueTyped program world after := by
  induction path generalizing before after with
  | nil => simp [Value.replace] at written
  | cons index path ih =>
      rcases Value.replace_cons_shape written with ⟨_,found,⟨_,rfl⟩ | ⟨child,changed,rfl,nested,rfl⟩⟩
      · exact typed.clear_field (List.getElem?_eq_some_iff.mp found).1
      · have nonempty : path ≠ [] := by intro empty; simp [empty,Value.replace] at nested
        have typeEq : changed.type = child.type := by
          simpa [Value.shell,Value.withFields,Value.type] using congrArg Value.type (Value.replace_shell nested nonempty)
        exact typed.replace_child found (ih (typed.child found) nested) typeEq

theorem World.clear_typed_roots {program : Kernel.Program} {before after typingWorld : World} {address : Address}
    (roots : ∀ id root resident, before.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type)
    (written : before.write address none = some after) :
    ∀ id root resident, after.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program typingWorld resident ∧ resident.type = root.type := by
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some original =>
      simp only [selected] at written
      dsimp at written
      split at written
      next empty =>
        have result := Option.some.inj written
        subst after
        intro id root resident present active contents
        by_cases same : address.root = id
        · subst id
          have rootEq : root = { original with value := none } := by simpa [Table.get_set] using present.symm
          subst root
          cases contents
        · exact roots id root resident (by simpa [Table.get_set_other,Ne.symm same] using present) active contents
      next nonempty =>
        cases resident : original.value with
        | none => simp [resident] at written
        | some whole =>
            simp only [resident] at written
            dsimp at written
            cases replaced : whole.replace address.fields none with
            | none => simp [replaced] at written
            | some changed =>
                have result : after = { before with roots := before.roots.set address.root { original with value := some changed } } := by
                  simpa [replaced] using written.symm
                subst after
                intro id root value present active contents
                by_cases same : address.root = id
                · subst id
                  have rootEq : root = { original with value := some changed } := by simpa [Table.get_set] using present.symm
                  subst root
                  cases Option.some.inj contents
                  have found := World.root_found selected
                  have checked := roots _ _ _ found.1 found.2.1 resident
                  refine ⟨checked.1.clear_path replaced,?_⟩
                  have pathNonempty : address.fields ≠ [] := by simpa using nonempty
                  have typeEq : changed.type = whole.type := by
                    simpa [Value.shell,Value.withFields,Value.type] using congrArg Value.type (Value.replace_shell replaced pathNonempty)
                  exact typeEq.trans checked.2
                · exact roots id root value (by simpa [Table.get_set_other,Ne.symm same] using present) active contents

theorem Typing.WorldTyped.roots {program : Kernel.Program} {world : World} (typed : Typing.WorldTyped program world) :
    ∀ id root resident, world.roots.get id = some root → root.live = true → root.value = some resident →
      Typing.ValueTyped program world resident ∧ resident.type = root.type := by
  intro id root resident found live contents
  exact ⟨typed.2.1 ⟨id,root.generation,[]⟩ resident ⟨root,resident,found,live,rfl,contents,.root⟩,
    typed.2.2.1 id root resident found contents⟩

/-- Both writes preserve all resulting resident trees, including ancestors
whose field lists changed. References are transported only after composing
clear and install, so no typed intermediate state is assumed. -/
theorem Transfers.typed_residents {program : Kernel.Program} {before after : World} {authority source destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (transfer : Transfers program.declarations before authority source destination after) :
    (∀ address value, after.Resident address value → Typing.ValueTyped program after value) ∧
    (∀ id root value, after.roots.get id = some root → root.live = true → root.value = some value → value.type = root.type) := by
  have moved := transfer
  cases transfer with
  | move stored _ _ _ separate located clear install =>
      obtain ⟨offset,located⟩ := located
      have destinationOutside : ¬ source.ProperPrefix destination := fun included => separate included.1.overlaps
      have framed := (World.write_address_offsets clear destinationOutside).mp located
      have roots := World.write_typed_roots valid inventory (World.clear_typed_roots typed.roots clear) framed install
        (fun value equal => by cases Option.some.inj equal; exact ⟨World.stores_typed typed.roots stored,rfl⟩)
      refine ⟨?_,fun id root value found live resident => (roots id root value found live resident).2⟩
      intro address value resident
      exact (World.stores_typed roots (World.resident_iff_stores.mp resident)).transfer typed.1 moved

end Glorious.Language
