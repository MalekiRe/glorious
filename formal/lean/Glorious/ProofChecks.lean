import Glorious.Effects

/-! Small kernel-reduced examples at the composed boundary. General claims
    live in the preceding modules' theorems; these examples only check that
    the executable definitions connect with the intended concrete outcomes. -/
namespace Glorious.ProofChecks

private def storage (n : Nat) : StorageId := ⟨n, []⟩
private def owner (n : Nat) : OwnerId := ⟨n⟩
private def hook : DeclId := ⟨0, 42⟩
private def affine (n : Nat) : Resident :=
  .owned (storage n) (owner n) .affine none []
private def exact (n : Nat) : Resident :=
  .owned (storage n) (owner n) .exact none []

theorem empty_scope : compileKnownExit 1 .normalReturn (.ok []) = .ok [] := rfl

theorem budget_is_not_empty :
    compileKnownExit 0 .normalReturn (.ok []) = .error .resourceLimit := rfl

theorem locals_reverse_creation :
    compileKnownExit 8 .normalReturn (.ok [affine 1, affine 2]) =
      .ok [.release (storage 2) (owner 2), .release (storage 1) (owner 1)] := rfl

theorem hook_before_reverse_fields_before_release :
    compileKnownExit 12 .normalReturn
      (.ok [.owned (storage 0) (owner 0) .affine (some hook) [affine 1, affine 2]]) =
      .ok [.hook (owner 0) hook, .release (storage 2) (owner 2),
        .release (storage 1) (owner 1), .release (storage 0) (owner 0)] := rfl

theorem partial_move_skips_vacancy :
    compileKnownExit 8 .properTail (.ok [affine 1, .vacant (storage 2)]) =
      .ok [.release (storage 1) (owner 1)] := rfl

theorem cancellation_cannot_lose_exact :
    compileKnownExit 8 .cancellation (.ok [exact 1]) = .error (.exactOwner (owner 1)) := rfl

theorem terminal_effect_cannot_lose_exact :
    compileKnownExit 8 (.terminalEffect ⟨0, 7⟩) (.ok [exact 1]) =
      .error (.exactOwner (owner 1)) := rfl

theorem label_cannot_leave_unique_hole :
    compileKnownExit 8 (.labelTransfer ⟨⟨0, 1⟩, 2⟩)
      (.ok [.openLoan (storage 1) ⟨8⟩]) =
      .error (.unrestoredLoan (storage 1) ⟨8⟩) := rfl

theorem zero_sized_manual_exact_stays_exact :
    compileKnownExit 8 .normalReturn
      (.ok [.owned (storage 1) (owner 1) .exact none []]) =
      .error (.exactOwner (owner 1)) := rfl

inductive ResultTag where
  | ok
  | err

/-- Failure is an ordinary returned tag, not an implicit rollback instruction. -/
theorem returned_error_keeps_poststate :
    Flow.bind (Flow.pure ([] : List Resident) ResultTag.err)
      (fun postState _ => Flow.pure postState ()) = Flow.pure [] () := by
  exact Flow.pure_bind _ _ _

theorem unknown_callback_cannot_supply_empty_cleanup :
    cleanupRoute 8 (⟨[], [exact 1], .unknown .missingContract⟩ : Route _ Unit) =
      .error (.missingEvidence .missingContract) := rfl

theorem exact_finite_is_not_ordinary_exact :
    ResumptionPolicy.tailResumeAllowed (.exact 2 (by decide) (by decide)) = false := rfl

end Glorious.ProofChecks
