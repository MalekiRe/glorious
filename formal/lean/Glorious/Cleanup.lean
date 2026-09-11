import Glorious.Control

/-! An executable, proof-producing cleanup compiler for language §7.6–7.7.
    The specification is the independent `Destroys` relation, not the result
    of running the compiler. The compiler must establish every premise before
    returning a plan. Proofs erase in the executable.

    Input is an already elaborated residual owner forest, in declaration order.
    Moves protect payloads by removing their residents from this forest first.
    This module does not infer types, decide transfer destinations, derive loan
    liveness, validate Drop bodies, or execute machine release/Drop hooks. -/
namespace Glorious

structure StorageId where
  allocation : Nat
  path : List Nat
  deriving DecidableEq, Repr, BEq

structure OwnerId where
  serial : Nat
  deriving DecidableEq, Repr, BEq

structure LoanId where
  serial : Nat
  deriving DecidableEq, Repr, BEq

/-- Storage identity survives a move; resident owner identity travels with the
    moved value. No byte count appears: zero-sized owners have the same rules. -/
inductive Resident where
  | vacant (storage : StorageId)
  | openLoan (storage : StorageId) (loan : LoanId)
  | owned (storage : StorageId) (owner : OwnerId) (principal : Principal)
      (dropHook : Option DeclId) (fields : List Resident)
  deriving Repr

inductive CleanupEvent where
  | hook (owner : OwnerId) (declaration : DeclId)
  | release (storage : StorageId) (owner : OwnerId)
  deriving DecidableEq, Repr, BEq

def hookEvents (owner : OwnerId) : Option DeclId → List CleanupEvent
  | none => []
  | some declaration => [.hook owner declaration]

mutual
  /-- A hook is called before reverse-order residual-field destruction and
      release. There is no rule for exact residents or open unique-loan holes. -/
  inductive Destroys : Resident → List CleanupEvent → Prop where
    | vacant (storage) : Destroys (.vacant storage) []
    | owned {storage owner principal hook fields events}
        (discardable : principal.MayDiscard)
        (children : DestroysFields fields events) :
        Destroys (.owned storage owner principal hook fields)
          (hookEvents owner hook ++ events ++ [.release storage owner])

  /-- The list is in declaration/creation order, not pre-reversed by a caller. -/
  inductive DestroysFields : List Resident → List CleanupEvent → Prop where
    | nil : DestroysFields [] []
    | cons {field fields fieldEvents restEvents}
        (rest : DestroysFields fields restEvents)
        (head : Destroys field fieldEvents) :
        DestroysFields (field :: fields) (restEvents ++ fieldEvents)
end

inductive CleanupError where
  | resourceLimit
  | exactOwner (owner : OwnerId)
  | unrestoredLoan (storage : StorageId) (loan : LoanId)
  | missingEvidence (reason : UnknownReason)
  deriving DecidableEq, Repr, BEq

abbrev CleanupPlan (resident : Resident) :=
  { events : List CleanupEvent // Destroys resident events }

abbrev ScopePlan (residents : List Resident) :=
  { events : List CleanupEvent // DestroysFields residents events }

mutual
  /-- Bounded proof search; exhaustion is not rejection on semantic grounds,
      and never yields a guessed plan. Fuel bounds structural descent. -/
  def compileResident : (fuel : Nat) → (r : Resident) → Except CleanupError (CleanupPlan r)
    | 0, _ => .error .resourceLimit
    | _ + 1, .vacant storage => .ok ⟨[], .vacant storage⟩
    | _ + 1, .openLoan storage loan => .error (.unrestoredLoan storage loan)
    | fuel + 1, .owned storage owner principal hook fields =>
      if h : principal.MayDiscard then
        match compileScope fuel fields with
        | .error problem => .error problem
        | .ok ⟨events, proof⟩ =>
          .ok ⟨hookEvents owner hook ++ events ++ [.release storage owner], .owned h proof⟩
      else .error (.exactOwner owner)

  def compileScope : (fuel : Nat) → (rs : List Resident) → Except CleanupError (ScopePlan rs)
    | 0, _ => .error .resourceLimit
    | _ + 1, [] => .ok ⟨[], .nil⟩
    | fuel + 1, field :: fields =>
      match compileScope fuel fields with
      | .error problem => .error problem
      | .ok ⟨restEvents, restProof⟩ =>
        match compileResident fuel field with
        | .error problem => .error problem
        | .ok ⟨fieldEvents, fieldProof⟩ =>
          .ok ⟨restEvents ++ fieldEvents, .cons restProof fieldProof⟩
end

theorem no_exact_destruction (storage owner hook fields events) :
    ¬ Destroys (.owned storage owner .exact hook fields) events := by
  intro h
  cases h with
  | owned permission _ => exact Principal.exact_not_discardable permission

theorem no_open_loan_destruction (storage loan events) :
    ¬ Destroys (.openLoan storage loan) events := by
  intro h
  cases h

theorem no_exact_plan (fuel storage owner hook fields)
    (plan : CleanupPlan (.owned storage owner .exact hook fields)) :
    compileResident fuel (.owned storage owner .exact hook fields) ≠ .ok plan := by
  exact False.elim (no_exact_destruction storage owner hook fields plan.val plan.property)

theorem compiled_resident_sound (fuel r) (plan : CleanupPlan r)
    (_h : compileResident fuel r = .ok plan) : Destroys r plan.val := plan.property

theorem compiled_scope_sound (fuel rs) (plan : ScopePlan rs)
    (_h : compileScope fuel rs = .ok plan) : DestroysFields rs plan.val := plan.property

/-- Every cleanup-bearing exit uses the same obligations. Fatal events and
    proven divergence are deliberately *not* members of this type. -/
inductive CleanupBoundary where
  | normalReturn
  | labelTransfer (target : Brand)
  | terminalEffect (operation : DeclId)
  | cancellation
  | failedInitialization
  | properTail
  deriving DecidableEq, Repr, BEq

structure ExitPlan (rs : List Resident) where
  boundary : CleanupBoundary
  cleanup : ScopePlan rs

def compileExit (fuel : Nat) (boundary : CleanupBoundary) (rs : List Resident) :
    Except CleanupError (ExitPlan rs) := do
  return ⟨boundary, ← compileScope fuel rs⟩

/-- Unknown control is never converted to an empty cleanup scope. -/
def compileKnownExit (fuel : Nat) (boundary : CleanupBoundary)
    (rs : Except UnknownReason (List Resident)) :
    Except CleanupError (List CleanupEvent) := do
  let rs ← rs.mapError CleanupError.missingEvidence
  let plan ← compileExit fuel boundary rs
  return plan.cleanup.val

theorem unknown_exit_rejected (fuel boundary reason) :
    compileKnownExit fuel boundary (.error reason) =
      .error (.missingEvidence reason) := rfl

/-- Producer/consumer connection: compute cleanup for each actual guarded
    outcome, without rerunning a source walker or flattening alternatives. -/
def cleanupRoute (fuel : Nat) (r : Route (List Resident) α) :
    Except CleanupError (List CleanupEvent) :=
  let finish boundary := compileKnownExit fuel boundary (.ok r.state)
  match r.outcome with
  | .normal _ => finish .normalReturn
  | .transfer target => finish (.labelTransfer target)
  | .terminalEffect op => finish (.terminalEffect op)
  | .cancelled => finish .cancellation
  | .fatal _ | .diverged | .suspended _ => .ok []
  | .unknown reason => .error (.missingEvidence reason)

end Glorious
