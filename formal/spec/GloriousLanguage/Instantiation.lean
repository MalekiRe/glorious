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

def EnvironmentAccess.mapTerms (f : Term → Term) (access : EnvironmentAccess) : EnvironmentAccess :=
  { access with region := f access.region, after := f access.after }

def Invocation.transformTerms (f : Term → Term) (signatures : Signature → Signature) (call : Invocation) : Invocation :=
  { call with
    signature := signatures call.signature
    environment := call.environment.map (EnvironmentAccess.mapTerms f) }

def Invocation.mapTerms (f : Term → Term) (call : Invocation) : Invocation :=
  call.transformTerms f (Signature.mapTerms f)

def Invocation.instantiate (call : Invocation) (substitution : Substitution) : Invocation :=
  call.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)

/-- Only the selected clause's header is closed here. Its body remains lexical
until execution enters it, including its fresh continuation binder. -/
def OperationArm.closeHead (scope : ScopeInstantiation) : OperationArm → OperationArm
  | .clause id family item patterns continuation body => .clause id
      (family.map scope.term) (item.map scope.term) (patterns.map (Pattern.mapTerms scope.term))
      continuation body

mutual
  /-- One structural traversal for runtime-name actions and generic
  instantiation. The latter supplies its distinct signature operation, which
  discharges generic binders instead of preserving their defaults. -/
  def Code.transformTerms (f : Term → Term) (signatures : Signature → Signature) : Code → Code
    | .result value => .result value
    | .bind localSlot value next => .bind (localSlot.mapTerms f) (value.mapTerms f) (next.transformTerms f signatures)
    | .evaluate localSlot value next => .evaluate (localSlot.mapTerms f)
        (value.transformTerms f signatures) (next.transformTerms f signatures)
    | .assign destination value next => .assign destination value (next.transformTerms f signatures)
    | .discard value next => .discard value (next.transformTerms f signatures)
    | .invoke localSlot call next => .invoke (localSlot.mapTerms f)
        (call.transformTerms f signatures) (next.transformTerms f signatures)
    | .tail call => .tail (call.transformTerms f signatures)
    | .scope id body => .scope id (body.transformTerms f signatures)
    | .label brand region result body => .label brand region (f result) (body.transformTerms f signatures)
    | .choose subject arms => .choose subject (arms.map (Arm.transformTerms f signatures))
    | .handle id computation handler => .handle id (computation.transformTerms f signatures) (handler.transformTerms f signatures)
    | .test localSlot subject pattern id next => .test (localSlot.mapTerms f) subject
        (pattern.mapTerms f) id (next.transformTerms f signatures)
    | .endLoan handle next => .endLoan handle (next.transformTerms f signatures)
    | .unsafeScope body => .unsafeScope (body.transformTerms f signatures)
    | .closeAvailable value next => .closeAvailable value (next.transformTerms f signatures)
    | .reserve localSlot brand places next => .reserve (localSlot.mapTerms f) brand places (next.transformTerms f signatures)
    | .abort => .abort

  def Arm.transformTerms (f : Term → Term) (signatures : Signature → Signature) : Arm → Arm
    | .clause pattern body => .clause (pattern.mapTerms f) (body.transformTerms f signatures)

  def OperationArm.transformTerms (f : Term → Term) (signatures : Signature → Signature) : OperationArm → OperationArm
    | .clause id family item patterns continuation body => .clause id
        (family.map f) (item.map f) (patterns.map (Pattern.mapTerms f))
        (continuation.map (Local.mapTerms f)) (body.transformTerms f signatures)

  def Handler.transformTerms (f : Term → Term) (signatures : Signature → Signature) : Handler → Handler
    | .attached result completion operations captures => .attached (f result)
        (completion.map (Arm.transformTerms f signatures)) (operations.map (OperationArm.transformTerms f signatures))
        (captures.map (Capture.mapTerms f))
end

def Code.mapTerms (f : Term → Term) : Code → Code := Code.transformTerms f (Signature.mapTerms f)
def Arm.mapTerms (f : Term → Term) : Arm → Arm := Arm.transformTerms f (Signature.mapTerms f)
def OperationArm.mapTerms (f : Term → Term) : OperationArm → OperationArm := OperationArm.transformTerms f (Signature.mapTerms f)
def Handler.mapTerms (f : Term → Term) : Handler → Handler := Handler.transformTerms f (Signature.mapTerms f)

def Code.instantiate (substitution : Substitution) : Code → Code :=
  Code.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)
def Arm.instantiate (substitution : Substitution) : Arm → Arm :=
  Arm.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)
def OperationArm.instantiate (substitution : Substitution) : OperationArm → OperationArm :=
  OperationArm.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)
def Handler.instantiate (substitution : Substitution) : Handler → Handler :=
  Handler.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)

def Function.transformTerms (f : Term → Term) (signatures : Signature → Signature) (function : Function) : Function :=
  { function with
    parameters := function.parameters.map (Local.mapTerms f)
    captures := function.captures.map (Local.mapTerms f)
    signature := signatures function.signature
    body := function.body.transformTerms f signatures }

def Function.mapTerms (f : Term → Term) (function : Function) : Function :=
  function.transformTerms f (Signature.mapTerms f)

def Function.instantiate (function : Function) (substitution : Substitution) : Function :=
  function.transformTerms (Term.substitute substitution) (fun signature => signature.instantiate substitution)

def Function.entryScope (function : Function) (region brand : Identity) : ScopeInstantiation :=
  ⟨[(function.activationRegion,region)],
    (match function.namedExit with | none => [] | some label => [(label,.label brand)])⟩

def Instance (program : Program) (id : DeclId) (arguments : List Term) (function : Function) : Prop :=
  ∃ template declaration substitution,
    program.function id = some template ∧ program.declarations.function id = some declaration ∧
    template.signature = declaration.signature ∧
    Instantiates template.signature.generics arguments substitution ∧
    ConstraintsHold program.declarations ⟨[],[],0,declaration.header.module,false,{}⟩ substitution template.signature.constraints ∧
    (∀ argument ∈ arguments, argument.ScopeClosed) ∧
    function = template.instantiate substitution

end Kernel
end Glorious.Language
