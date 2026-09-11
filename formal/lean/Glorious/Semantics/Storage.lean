import Glorious.Semantics.Core

namespace Glorious.Semantics

structure Address where
  slot : Id
  fields : List Nat := []
  deriving BEq, DecidableEq, Repr, Inhabited

def overlaps (a b : Address) : Bool :=
  a.slot == b.slot && (a.fields.isPrefixOf b.fields || b.fields.isPrefixOf a.fields)

structure Pointer where
  allocation : Option Id
  offset : Int
  provenance : Option Id
  mutable : Bool
  source : Option Address := none
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ValueHead where
  | unit
  | scalar (value : ScalarValue)
  | constructor (declaration : Option DeclId)
  | callable (declaration : DeclId) (arguments : List Term) (materialized : Bool)
  | operation (declaration : DeclId) (arguments : List Term)
  | reference (loan : Id)
  | pointer (pointer : Pointer)
  | label (brand : Term)
  | continuation (identity : Id)
  | available (brand : Term)
  | bindingPack (brand : Term)
  | staticView (segment : Id) (length : Nat)
  | symbolic (origin : Id)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One logical owner; its children are inline residents, not reference
    pointees. Partial initialization is represented by `none`, never by a
    fabricated value. Captures occupy these same resident fields. -/
inductive Value where
  | owned (identity : Id) (type : Term) (capability : Principal)
      (dropHook : Option DeclId) (shellConsumed : Bool)
      (head : ValueHead) (fields : List (Option Value))
  deriving BEq, Repr

def Value.identity : Value → Id | .owned identity .. => identity
def Value.type : Value → Term | .owned _ type .. => type
def Value.capability : Value → Principal | .owned _ _ capability .. => capability
def Value.dropHook : Value → Option DeclId | .owned _ _ _ hook .. => hook
def Value.head : Value → ValueHead | .owned _ _ _ _ _ head _ => head
def Value.fields : Value → List (Option Value) | .owned _ _ _ _ _ _ fields => fields
def Value.shellConsumed : Value → Bool | .owned _ _ _ _ consumed .. => consumed

def Value.withFields (value : Value) (fields : List (Option Value)) (consumed : Bool := false) : Value :=
  match value with
  | .owned id type capability hook shell head _ => .owned id type capability hook (shell || consumed) head fields

def Value.withHead (value : Value) (head : ValueHead) : Value :=
  match value with
  | .owned id type capability hook shell _ fields => .owned id type capability hook shell head fields

def valueTree : Nat → Value → Check (List Value)
  | 0, _ => reject .resourceLimit "resident traversal exhausted"
  | fuel + 1, value => return value :: (← value.fields.filterMap id |>.mapM (valueTree fuel)).flatten

def fullyInitialized (fuel : Nat) (value : Value) : Check Bool := do
  let values ← valueTree fuel value
  return values.all (fun resident => resident.fields.all Option.isSome)

structure Slot where
  declaration : TypedSlot
  frame : Id
  scope : Id
  storage : StorageId
  value : Option Value := none
  deriving Repr

structure Loan where
  identity : Id
  origin : Address
  referent : Term
  region : Term
  mode : Mutability
  parent : Option Id
  live : Bool := true
  hole : Bool := false
  deriving BEq, Repr

structure Allocation where
  identity : Id
  provenance : Id
  domain : Id
  size : Nat
  alignment : Nat
  alive : Bool
  initialized : List (Nat × Nat)
  byteValues : List (Nat × UInt8)
  residents : List (Nat × Value) := []
  deriving Repr

structure LabelState where
  brand : Term
  region : Term
  result : Term
  frame : Id
  scope : Id
  deriving Repr

structure Availability where
  brand : Term
  origin : Id
  guardedOwners : List Id
  pending : Bool
  deriving Repr

structure World where
  slots : List Slot := []
  loans : List Loan := []
  labels : List LabelState := []
  availability : List Availability := []
  allocations : List Allocation := []
  nextOwner : Id := 0
  nextLoan : Id := 0
  nextAllocation : Id := 0
  frame : Id := 0
  scope : Id := 0
  guards : List Guard := []
  cleanup : List CleanupEvent := []
  effects : List Term := []
  deriving Repr

abbrev WorldM := StateT World Check

def getSlot (world : World) (identity : Id) : Check Slot :=
  getRequired (world.slots.find? (fun s => s.declaration.id == identity)) .uninitialized "unknown storage slot"

def setSlot (slot : Slot) : WorldM Unit :=
  modify fun world => { world with slots := world.slots.map (fun s => if s.declaration.id == slot.declaration.id then slot else s) }

def declareSlot (declaration : TypedSlot) : WorldM Unit := do
  let world ← get
  require (!(world.slots.any (fun slot => slot.declaration.id == declaration.id))) .duplicate "slot identity already exists" declaration.span
  let storage : StorageId := ⟨world.nextAllocation, []⟩
  set { world with nextAllocation := world.nextAllocation + 1,
    slots := world.slots ++ [⟨declaration, world.frame, world.scope, storage, none⟩] }

def createValue (program : Program) (inference : Inference) (type : Term) (head : ValueHead)
    (fields : List (Option Value) := []) : WorldM Value := do
  let capability ← deriveUse program inference type
  let hook := match type with
    | .nominal declaration _ => (program.dataType declaration).bind (·.dropHook)
    | _ => none
  let world ← get
  set { world with nextOwner := world.nextOwner + 1 }
  return .owned world.nextOwner type capability hook false head fields

def fieldTypes (program : Program) (type : Term) (head : ValueHead) : Check (List Term) := do
  match type with
  | .unit => return []
  | .tuple fields => return fields
  | .array element (.constant (.integer _ _ count)) =>
    require (count ≥ 0 && count.toNat ≤ program.limits.alternatives) .resourceLimit "fixed-array resident expansion exceeds declared limit"
    return List.replicate count.toNat element
  | .nominal declaration arguments =>
    let data ← getRequired (program.dataType declaration) .unknownName "unknown nominal resident"
    let variant ← match head with
      | .constructor (some tag) => getRequired (data.variants.find? (fun v => v.header.id == tag)) .typeMismatch "invalid enum tag"
      | _ =>
        require (!data.isEnum && data.variants.length == 1) .missingEvidence "enum payload requires a checked active variant"
        getRequired data.variants.head? .invalidLayout "record has no constructor"
    let subs ← bindArguments data.generics arguments
    variant.fields.mapM (fun f => substitute program.limits.normalization subs f.type)
  | .callable .. => return [] -- callable capture types come from CoreFunction
  | _ => return []

def getAt : Nat → Value → List Nat → Check (Option Value)
  | 0, _, _ => reject .resourceLimit "place projection exhausted"
  | _ + 1, value, [] => return some value
  | fuel + 1, value, index :: rest => do
    let field ← getRequired value.fields[index]? .uninitialized "field projection is out of bounds"
    match field with
    | none => if rest.isEmpty then return none else reject .uninitialized "projection passes through an uninitialized field"
    | some field => getAt fuel field rest

def replaceAt : Nat → Value → List Nat → Option Value → Check Value
  | 0, _, _, _ => reject .resourceLimit "place update exhausted"
  | _, _, [], _ => reject .malformedCore "root replacement must update its slot"
  | fuel + 1, value, index :: rest, replacement => do
    let field ← getRequired value.fields[index]? .uninitialized "field update is out of bounds"
    let replacement ← if rest.isEmpty then pure replacement else do
      let child ← getRequired field .uninitialized "field update passes through an uninitialized resident"
      pure (some (← replaceAt fuel child rest replacement))
    return value.withFields (value.fields.set index replacement)

def lookupAddress (program : Program) (world : World) (address : Address) : Check (Option Value) := do
  let slot ← getSlot world address.slot
  match slot.value with
  | none => if address.fields.isEmpty then return none else reject .uninitialized "projection from an uninitialized owner"
  | some value => getAt program.limits.normalization value address.fields

def updateAddress (program : Program) (address : Address) (value : Option Value) : WorldM Unit := do
  let slot ← getSlot (← get) address.slot
  if address.fields.isEmpty then setSlot { slot with value }
  else
    let parent ← getRequired slot.value .uninitialized "field owner is uninitialized"
    let parent ← replaceAt program.limits.normalization parent address.fields value
    setSlot { slot with value := some parent }

structure Located where
  address : Address
  type : Term
  throughLoan : Option Id
  deriving Repr

def locate (program : Program) (world : World) (place : Place) : Check Located := do
  let slot ← getSlot world place.root
  let rec descend : Nat → Located → List Projection → Check Located
    | 0, _, _ => reject .resourceLimit "place resolution exhausted"
    | _, located, [] => return located
    | fuel + 1, located, projection :: rest => do
      let resident ← lookupAddress program world located.address
      match projection with
      | .dereference =>
        let value ← getRequired resident .uninitialized "dereferencing an uninitialized reference handle"
        match value.head with
        | .reference identity =>
          let loan ← getRequired (world.loans.find? (fun l => l.identity == identity && l.live)) .escapingReference "reference loan is no longer live"
          descend fuel ⟨loan.origin, loan.referent, some identity⟩ rest
        | _ => reject .unsafeOperation "raw pointer dereference must use the admitted memory operation"
      | .variant declaration =>
        let value ← getRequired resident .uninitialized "enum is uninitialized"
        require (value.head == .constructor (some declaration)) .typeMismatch "enum payload lacks matching structural guard"
        descend fuel located rest
      | .field index | .index index =>
        let value ← getRequired resident .uninitialized "field owner is uninitialized"
        let types ← fieldTypes program located.type value.head
        let type ← getRequired types[index]? .typeMismatch "field index is outside the declared shape"
        descend fuel { located with address.fields := located.address.fields ++ [index], type } rest
      | .dynamicIndex identity =>
        let indexSlot ← getSlot world identity
        let indexValue ← getRequired indexSlot.value .uninitialized "index is uninitialized"
        match indexValue.head with
        | .scalar (.integer _ _ index) =>
          require (index ≥ 0) .invalidPointer "negative array index"
          descend fuel located (.index index.toNat :: rest)
        | _ => reject .missingEvidence "dynamic place requires branch-correlated index expansion"
  descend program.limits.normalization ⟨⟨place.root, []⟩, slot.declaration.type, none⟩ place.projections

inductive Access where
  | read | write | move | destroy | sharedBorrow | uniqueBorrow
  deriving BEq, DecidableEq, Repr

def loanAncestor (fuel : Nat) (loans : List Loan) (ancestor child : Id) : Bool :=
  match fuel with
  | 0 => false
  | n + 1 =>
    if ancestor == child then true else
      match loans.find? (fun l => l.identity == child) with
      | none => false
      | some loan => match loan.parent with | none => false | some parent => loanAncestor n loans ancestor parent

def checkAccess (program : Program) (world : World) (located : Located) (access : Access) : Check Unit := do
  let write := access == .write || access == .move || access == .destroy || access == .uniqueBorrow
  match located.throughLoan with
  | none => pure ()
  | some identity =>
    let loan ← getRequired (world.loans.find? (fun l => l.identity == identity && l.live)) .escapingReference "access uses an ended loan"
    require (!write || loan.mode == .unique) .loanConflict "shared loan does not permit ownership or mutation"
    require (!loan.hole || access == .write) .loanHole "a unique-reference hole must be restored before this operation"
  for loan in world.loans do
    if loan.live && overlaps located.address loan.origin then
      let through := match located.throughLoan with
        | none => false
        | some identity => loanAncestor program.limits.normalization world.loans loan.identity identity
      if !through then
        require (!write && loan.mode == .shared) .loanConflict "access conflicts with a live loan"

def checkHandle (world : World) (value : Value) : Check Unit := do
  match value.head with
  | .reference identity =>
    let loan ← getRequired (world.loans.find? (fun l => l.identity == identity && l.live)) .escapingReference "reference handle outlived its loan"
    require (!loan.hole) .loanHole "a reference handle with an initialization hole cannot be read, moved or ended"
  | _ => pure ()

def checkFieldMove (program : Program) (world : World) (address : Address) : Check Unit := do
  let slot ← getSlot world address.slot
  let rec inspect : Nat → Option Value → List Nat → Check Unit
    | 0, _, _ => reject .resourceLimit "field-move authorization exhausted"
    | _, _, [] => return ()
    | fuel + 1, resident, index :: rest => do
      let resident ← getRequired resident .uninitialized "partial move from an uninitialized parent"
      require resident.dropHook.isNone .illegalDiscard "safe partial move from a custom-Drop owner"
      let child ← getRequired resident.fields[index]? .uninitialized "partial move field is absent"
      inspect fuel child rest
  inspect program.limits.normalization slot.value address.fields

def cloneValue : Nat → Value → WorldM Value
  | 0, _ => reject .resourceLimit "structural copy exhausted"
  | fuel + 1, value => do
    require (value.capability == .duplicable) .illegalCopy "source type does not permit structural ownership duplication"
    checkHandle (← get) value
    let fields ← value.fields.mapM (fun field => field.mapM (cloneValue fuel))
    let world ← get
    set { world with nextOwner := world.nextOwner + 1 }
    return .owned world.nextOwner value.type value.capability value.dropHook value.shellConsumed value.head fields

def takeValue (program : Program) (place : Place) (forcedMove : Bool := true) : WorldM Value := do
  let world ← get
  let located ← locate program world place
  let value ← lookupAddress program world located.address >>= fun v => getRequired v .moved "read of an unavailable owner"
  checkHandle world value
  require (← fullyInitialized program.limits.normalization value) .uninitialized "whole use of a partially initialized owner"
  if !forcedMove && value.capability == .duplicable then
    checkAccess program world located .read
    cloneValue program.limits.normalization value
  else
    checkAccess program world located .move
    checkFieldMove program world located.address
    updateAddress program located.address none
    match located.throughLoan with
    | none => pure ()
    | some identity => modify fun s => { s with loans := s.loans.map fun loan =>
        if loan.identity == identity then { loan with hole := true } else loan }
    return value

def initializeValue (program : Program) (destination : Place) (value : Value) : WorldM Unit := do
  let world ← get
  let located ← locate program world destination
  require (located.type == value.type) .typeMismatch "initialization changes the declared resident type"
  require (← lookupAddress program world located.address |>.map Option.isNone) .uninitialized "initialization would overwrite a live owner"
  checkAccess program world located .write
  updateAddress program located.address (some value)
  modify fun s => { s with loans := s.loans.map fun loan =>
    if loan.live && loan.origin == located.address then { loan with hole := false } else loan }

def borrowValue (program : Program) (inference : Inference) (source : Place)
    (mode : Mutability) (region : Term) : WorldM Value := do
  let world ← get
  let located ← locate program world source
  let value ← lookupAddress program world located.address >>= fun v => getRequired v .uninitialized "borrowing an unavailable resident"
  require (← fullyInitialized program.limits.normalization value) .loanHole "borrowing a partially initialized resident"
  checkAccess program world located (if mode == .shared then .sharedBorrow else .uniqueBorrow)
  let loan : Loan := ⟨world.nextLoan, located.address, located.type, region, mode, located.throughLoan, true, false⟩
  set { world with nextLoan := world.nextLoan + 1, loans := world.loans ++ [loan] }
  createValue program inference (.reference mode region located.type) (.reference loan.identity)

def endLoan (identity : Id) : WorldM Unit := do
  let world ← get
  let loan ← getRequired (world.loans.find? (fun l => l.identity == identity && l.live)) .missingEvidence "cannot end an unknown or ended loan"
  require (!loan.hole) .loanHole "ending a loan with an unrestored hole"
  require (!(world.loans.any (fun l => l.live && l.parent == some identity))) .loanConflict "parent loan still has live reborrows"
  set { world with loans := world.loans.map fun l => if l.identity == identity then { l with live := false } else l }

def valueResident (program : Program) (world : World) : Nat → StorageId → Value → Check Resident
  | 0, _, _ => reject .resourceLimit "cleanup resident projection exhausted"
  | fuel + 1, storage, value => do
    match value.head with
    | .reference identity =>
      match world.loans.find? (fun l => l.identity == identity && l.live && l.hole) with
      | some _ => return .openLoan storage ⟨identity⟩
      | none => pure ()
    | _ => pure ()
    let fields ← value.fields.zipIdx |>.mapM fun (child, index) => do
      let fieldStorage := { storage with path := storage.path ++ [index] }
      match child with
      | none => pure (.vacant fieldStorage)
      | some resident => valueResident program world fuel fieldStorage resident
    let capability := if value.shellConsumed then .duplicable else value.capability
    return .owned storage ⟨value.identity⟩ capability value.dropHook fields

def discardValue (program : Program) (place : Place) : WorldM Unit := do
  let world ← get
  let located ← locate program world place
  checkAccess program world located .destroy
  let slot ← getSlot world located.address.slot
  let value ← lookupAddress program world located.address >>= fun v => getRequired v .moved "destruction of an unavailable resident"
  let storage := { slot.storage with path := slot.storage.path ++ located.address.fields }
  let resident ← valueResident program world program.limits.normalization storage value
  let plan ← (compileResident program.limits.analysis resident).mapError fun problem =>
    ⟨match problem with | .resourceLimit => .resourceLimit | .unrestoredLoan .. => .loanHole | _ => .illegalDiscard,
      slot.declaration.span, s!"unlawful cleanup: {repr problem}", []⟩
  updateAddress program located.address none
  modify fun world => { world with cleanup := world.cleanup ++ plan.val }

def assignValue (program : Program) (destination : Place) (value : Value) : WorldM Unit := do
  let world ← get
  let located ← locate program world destination
  let slot ← getSlot world located.address.slot
  require (located.throughLoan.isSome || slot.declaration.mutable) .invalidSource "assignment to an immutable binding"
  checkAccess program world located .write
  if (← lookupAddress program world located.address).isSome then discardValue program destination
  initializeValue program destination value

def allValues (program : Program) (world : World) : Check (List Value) := do
  return (← world.slots.filterMap (·.value) |>.mapM (valueTree program.limits.normalization)).flatten

def validateWorld (program : Program) (world : World) : Check Unit := do
  require (unique (world.slots.map (fun s => s.declaration.id))) .duplicate "duplicate storage-slot identity"
  require (unique (world.slots.map (·.storage))) .duplicate "distinct slots share a storage identity"
  let values ← allValues program world
  require (unique (values.map Value.identity)) .duplicateOwner "the same logical owner is resident in multiple locations"
  require (values.all (fun value => value.identity < world.nextOwner)) .malformedCore "owner identity is not allocated"
  require (unique (world.loans.map (·.identity))) .duplicate "duplicate logical loan identity"
  for loan in world.loans.filter (·.live) do
    require (loan.identity < world.nextLoan) .malformedCore "loan identity is not allocated"
    let origin ← lookupAddress program world loan.origin
    require (loan.hole || origin.isSome) .escapingReference "live loan has no initialized referent"
  require (consistentGuards world.guards) .malformedCore "inconsistent guarded resource state"

def sealValues (program : Program) (values : List Value) : WorldM Unit := do
  let world ← get
  let reachable ← values.mapM (valueTree program.limits.normalization)
  let reachable := reachable.flatten
  for value in reachable do
    match value.head with
    | .available brand | .bindingPack brand =>
      require (!(world.availability.any (fun a => a.brand == brand && a.pending)))
        .openAvailability "unresolved guarded environment cannot escape into plain storage"
    | .label brand =>
      require (world.labels.any (fun label => label.brand == brand)) .escapingBrand "label brand is not active"
    | .reference identity => checkHandle world value
    | _ => pure ()

def cleanupSlots (program : Program) (ending : List Id) (protected : List Value)
    (boundary : CleanupBoundary) : WorldM Unit := do
  let world ← get
  let protectedIds := (← protected.mapM (valueTree program.limits.normalization)).flatten.map Value.identity
  for loan in world.loans.filter (·.live) do
    if ending.contains loan.origin.slot then
      require (!loan.hole) .loanHole "cleanup-bearing exit ends an unrestored unique loan"
      let surviving := world.slots.filter (fun s => !ending.contains s.declaration.id) |>.filterMap (·.value)
      let carriers := (← (protected ++ surviving).mapM (valueTree program.limits.normalization)).flatten
      require (!(carriers.any (fun value => value.head == .reference loan.identity)))
        .escapingReference "a surviving reference points into reclaimed local storage"
  let residents ← world.slots.filter (fun s => ending.contains s.declaration.id) |>.mapM fun slot => do
    match slot.value with
    | none => pure (.vacant slot.storage)
    | some value =>
      require (!(protectedIds.contains value.identity)) .duplicateOwner "protected payload is still resident in the ending scope"
      valueResident program world program.limits.normalization slot.storage value
  let plan ← (compileExit program.limits.analysis boundary residents).mapError fun problem =>
    ⟨match problem with | .resourceLimit => .resourceLimit | .unrestoredLoan .. => .loanHole | _ => .illegalDiscard,
      {}, s!"unlawful exit cleanup: {repr problem}", []⟩
  set { world with
    slots := world.slots.filter (fun s => !ending.contains s.declaration.id)
    loans := world.loans.map (fun loan => if ending.contains loan.origin.slot then { loan with live := false } else loan)
    cleanup := world.cleanup ++ plan.cleanup.val }

end Glorious.Semantics
