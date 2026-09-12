import GloriousLanguage.Instantiation

/-! Destructor selection retains the nominal instance and its actual loan
region. Declaration admissibility and runtime body instantiation are separate;
both consume the ordinary kinded substitution and function-instance relations. -/
namespace Glorious.Language

def DropSignature (self region : Term) (signature : Signature) : Prop :=
  signature.parameters = [.reference .unique region self] ∧ signature.result = .unit ∧
  signature.effects = .row [] [] ∧ signature.unsafeAllowed = false

/-- A checked application of the real destructor declaration. Its generic
argument order comes from its signature, not the nominal type's spelling or
a convention that omits the independent reference region. -/
inductive DropApplication (program : Program) (self region : Term) (hook : DeclId) :
    List Term → FunctionDefinition → Substitution → Prop where
  | selected {arguments declaration substitution anchor} :
      DropHook program self (some hook) → program.function hook = some declaration →
      declaration.origin = .source anchor → declaration.captures = [] →
      Kinding program ⟨[],[],0,declaration.header.module,false⟩ region .region →
      Instantiates declaration.signature.generics arguments substitution →
      ConstraintsHold program ⟨[],[],0,declaration.header.module,false⟩ substitution declaration.signature.constraints →
      DropSignature self region (declaration.signature.instantiate substitution) →
      DropApplication program self region hook arguments declaration substitution

/-- Nonvacuous declaration admission: every actual nominal application in
the declaration's domain and every admitted borrowing region must select an
exact destructor signature. This supplies no executable body or runtime world. -/
def DropApplications (program : Program) : Prop :=
  ∀ id data hook arguments substitution region,
    program.data id = some data → data.dropHook = some hook →
    Instantiates data.generics arguments substitution →
    (∀ argument ∈ arguments, Kinding program ⟨[],[],0,data.header.module,false⟩ argument argument.kind) →
    ConstraintsHold program ⟨[],[],0,data.header.module,false⟩ substitution data.requirements →
    Kinding program ⟨[],[],0,data.header.module,false⟩ region .region →
    ∃ hookArguments declaration hookSubstitution,
      DropApplication program (.nominal id arguments) region hook hookArguments declaration hookSubstitution

namespace Kernel

def DropFunction (self region : Term) (function : Function) : Prop :=
  DropSignature self region function.signature ∧ function.captures = [] ∧
    function.parameters.map (·.type) = function.signature.parameters

/-- This is the actual selected invocation consumed by destruction. The
generic body is obtained through Instance, exactly as for ordinary calls. -/
def DropInstance (program : Kernel.Program) (self region : Term) (hook : DeclId) (function : Function) : Prop :=
  DropHook program.declarations self (some hook) ∧
    (∃ arguments, Instance program hook arguments function) ∧ DropFunction self region function

theorem DropFunction.parameter {self region : Term} {function : Function}
    (selected : DropFunction self region function) :
    ∃ formal, function.parameters = [formal] ∧ formal.type = .reference .unique region self := by
  have types := selected.2.2.trans selected.1.1
  cases parameters : function.parameters with
  | nil => simp [parameters] at types
  | cons formal rest =>
    cases rest with
    | nil => exact ⟨formal,rfl,by simpa [parameters] using types⟩
    | cons => simp [parameters] at types

/-- The body inventory supplies the selected source body. Neither a
pre-instantiated Function nor an executable dispatch is an admission premise. -/
theorem DropApplication.body {program : Kernel.Program} {self region : Term} {hook : DeclId}
    {arguments : List Term} {declaration : FunctionDefinition} {substitution : Substitution}
    (inventory : BodyInventory program)
    (selected : Language.DropApplication program.declarations self region hook arguments declaration substitution) :
    ∃ function, Instance program hook arguments function ∧
      DropSignature self region function.signature ∧ function.captures = [] := by
  cases selected with
  | selected hookFound found origin noCaptures _ instantiated constraints signature =>
    have lookup : program.declarations.lookup hook = some (.function declaration) := by
      unfold Language.Program.function at found
      cases lookedUp : program.declarations.lookup hook with
      | none => simp [lookedUp] at found
      | some definition => cases definition <;> simp_all
    have declarationId : declaration.header.id = hook := by
      have matching := List.find?_some lookup
      change (declaration.header.id.package == hook.package && declaration.header.id.serial == hook.serial) = true at matching
      simp only [Bool.and_eq_true,beq_iff_eq] at matching
      cases identity : declaration.header.id
      cases hook
      simp_all
    have lookupById : program.declarations.function declaration.header.id = some declaration := by
      simpa only [declarationId] using found
    obtain ⟨template,member,identity⟩ := inventory.2.2.1 declaration _ lookupById origin
    have present : (program.function hook).isSome = true := by
      unfold Program.function
      cases selected : program.functions.find? (fun body => body.declaration == hook) with
      | none =>
        have absent := List.find?_eq_none.mp selected template member
        rw [identity,declarationId] at absent
        change ¬(hook.package == hook.package && hook.serial == hook.serial) = true at absent
        simp at absent
      | some => rfl
    obtain ⟨body,bodyAt⟩ := Option.isSome_iff_exists.mp present
    have bodyId : body.declaration = hook := by
      have matching := List.find?_some bodyAt
      change (body.declaration.package == hook.package && body.declaration.serial == hook.serial) = true at matching
      simp only [Bool.and_eq_true,beq_iff_eq] at matching
      cases identity : body.declaration
      cases hook
      simp_all
    obtain ⟨actual,actualAt,bodySignature,_,bodyCaptures⟩ := inventory.2.1 body (List.mem_of_find?_eq_some bodyAt)
    rw [bodyId] at actualAt
    have same := Option.some.inj (actualAt.symm.trans found)
    subst actual
    have captures : body.captures = [] := by
      apply List.map_eq_nil_iff.mp
      exact bodyCaptures.trans noCaptures
    refine ⟨body.instantiate substitution,⟨body,declaration,substitution,bodyAt,found,bodySignature,?_,?_,rfl⟩,?_,?_⟩
    · simpa only [bodySignature] using instantiated
    · simpa only [bodySignature] using constraints
    · simpa only [Function.instantiate,Function.transformTerms,bodySignature] using signature
    · simp [Function.instantiate,Function.transformTerms,captures]

end Kernel
end Glorious.Language
