import GloriousLanguage.Kernel

/-! Runtime instances substitute the same kinded terms throughout a body.
This is not a second inference procedure. A substitution is admitted only
after the declaration's domain obligations have been discharged. -/
namespace Glorious.Language

def Signature.instantiate (signature : Signature) (substitution : Substitution) : Signature :=
  { signature with
    generics := []
    parameters := signature.parameters.map (Term.substitute substitution)
    result := signature.result.substitute substitution
    effects := signature.effects.substitute substitution
    constraints := signature.constraints.map (Constraint.substitute substitution) }

namespace Kernel

def Local.mapTerms (f : Term → Term) (localSlot : Local) : Local := { localSlot with type := f localSlot.type }
def Capture.mapTerms (f : Term → Term) (capture : Capture) : Capture := { capture with type := f capture.type }

def Pattern.mapTerms (f : Term → Term) : Pattern → Pattern
  | .bind localSlot => .bind (localSlot.mapTerms f)
  | .tuple fields => .tuple (fields.map (Pattern.mapTerms f))
  | .array fields => .array (fields.map (Pattern.mapTerms f))
  | .constructor id fields => .constructor id (fields.map (Pattern.mapTerms f))
  | .reference mode pattern => .reference mode (pattern.mapTerms f)
  | pattern => pattern

def Atom.mapTerms (f : Term → Term) : Atom → Atom
  | .constant value => .constant (f value)
  | .borrow source mode region => .borrow source mode (f region)
  | .label brand => .label (f brand)
  | .construct type variant fields => .construct (f type) variant fields
  | .closure id arguments captures => .closure id (arguments.map f) (captures.map (Capture.mapTerms f))
  | .function id arguments => .function id (arguments.map f)
  | .operation id family item => .operation id (family.map f) (item.map f)
  | .primitive id arguments operands => .primitive id (arguments.map f) operands
  | atom => atom

def Invocation.instantiate (call : Invocation) (substitution : Substitution) : Invocation :=
  { call with signature := call.signature.instantiate substitution }

/-- Only the selected clause's header is closed here. Its body remains lexical
until execution enters it, including its fresh continuation binder. -/
def OperationArm.closeHead (scope : ScopeInstantiation) : OperationArm → OperationArm
  | .clause id family item patterns continuation body => .clause id
      (family.map scope.term) (item.map scope.term) (patterns.map (Pattern.mapTerms scope.term))
      continuation body

mutual
  def Code.instantiate (substitution : Substitution) : Code → Code
    | .result value => .result value
    | .bind localSlot value next => .bind (localSlot.mapTerms (Term.substitute substitution))
        (value.mapTerms (Term.substitute substitution)) (next.instantiate substitution)
    | .evaluate localSlot value next => .evaluate (localSlot.mapTerms (Term.substitute substitution))
        (value.instantiate substitution) (next.instantiate substitution)
    | .assign destination value next => .assign destination value (next.instantiate substitution)
    | .discard value next => .discard value (next.instantiate substitution)
    | .invoke localSlot call next => .invoke (localSlot.mapTerms (Term.substitute substitution))
        (call.instantiate substitution) (next.instantiate substitution)
    | .tail call => .tail (call.instantiate substitution)
    | .scope id body => .scope id (body.instantiate substitution)
    | .label brand region result body => .label brand region (result.substitute substitution) (body.instantiate substitution)
    | .choose subject arms => .choose subject (arms.map (Arm.instantiate substitution))
    | .handle id computation handler => .handle id (computation.instantiate substitution) (handler.instantiate substitution)
    | .test localSlot subject pattern id next => .test (localSlot.mapTerms (Term.substitute substitution)) subject
        (pattern.mapTerms (Term.substitute substitution)) id (next.instantiate substitution)
    | .endLoan handle next => .endLoan handle (next.instantiate substitution)
    | .unsafeScope body => .unsafeScope (body.instantiate substitution)
    | .closeAvailable value next => .closeAvailable value (next.instantiate substitution)
    | .reserve localSlot brand places next => .reserve (localSlot.mapTerms (Term.substitute substitution)) brand places (next.instantiate substitution)
    | .abort => .abort

  def Arm.instantiate (substitution : Substitution) : Arm → Arm
    | .clause pattern body => .clause (pattern.mapTerms (Term.substitute substitution)) (body.instantiate substitution)

  def OperationArm.instantiate (substitution : Substitution) : OperationArm → OperationArm
    | .clause id family item patterns continuation body => .clause id
        (family.map (Term.substitute substitution)) (item.map (Term.substitute substitution))
        (patterns.map (Pattern.mapTerms (Term.substitute substitution)))
        (continuation.map (Local.mapTerms (Term.substitute substitution))) (body.instantiate substitution)

  def Handler.instantiate (substitution : Substitution) : Handler → Handler
    | .attached result completion operations captures => .attached (result.substitute substitution)
        (completion.map (Arm.instantiate substitution)) (operations.map (OperationArm.instantiate substitution))
        (captures.map (Capture.mapTerms (Term.substitute substitution)))
end

def Function.instantiate (function : Function) (substitution : Substitution) : Function :=
  { function with
    parameters := function.parameters.map (Local.mapTerms (Term.substitute substitution))
    captures := function.captures.map (Local.mapTerms (Term.substitute substitution))
    signature := function.signature.instantiate substitution
    body := function.body.instantiate substitution }

def Function.entryScope (function : Function) (region brand : Identity) : ScopeInstantiation :=
  ⟨[(function.activationRegion,region)],
    (match function.namedExit with | none => [] | some label => [(label,.label brand)])⟩

def Instance (program : Program) (id : DeclId) (arguments : List Term) (function : Function) : Prop :=
  ∃ template declaration substitution,
    program.function id = some template ∧ program.declarations.function id = some declaration ∧
    template.signature = declaration.signature ∧
    Instantiates template.signature.generics arguments substitution ∧
    ConstraintsHold program.declarations ⟨[],[],0,declaration.header.module,false⟩ substitution template.signature.constraints ∧
    function = template.instantiate substitution

end Kernel
end Glorious.Language
