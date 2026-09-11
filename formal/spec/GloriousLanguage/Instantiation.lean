import GloriousLanguage.Kernel

/-! Runtime instances substitute the same kinded terms throughout a body.
This is not a second inference procedure. A substitution is admitted only
after the declaration's domain obligations have been discharged. -/
namespace Glorious.Language

def Term.substitute (substitution : Substitution) : Term → Term
  | .parameter id kind => (substitution.get id).getD (.parameter id kind)
  | .tuple fields => .tuple (fields.map (Term.substitute substitution))
  | .array a b => .array (a.substitute substitution) (b.substitute substitution)
  | .reference mode a b => .reference mode (a.substitute substitution) (b.substitute substitution)
  | .rawPointer mode a => .rawPointer mode (a.substitute substitution)
  | .nominal id arguments => .nominal id (arguments.map (Term.substitute substitution))
  | .alias id arguments => .alias id (arguments.map (Term.substitute substitution))
  | .callable id arguments => .callable id (arguments.map (Term.substitute substitution))
  | .continuation a b c d quantity => .continuation (a.substitute substitution) (b.substitute substitution)
      (c.substitute substitution) (d.substitute substitution) quantity
  | .label a b c => .label (a.substitute substitution) (b.substitute substitution) (c.substitute substitution)
  | .environment a b => .environment (a.substitute substitution) (b.substitute substitution)
  | .available a b => .available (a.substitute substitution) (b.substitute substitution)
  | .bindings a b arguments => .bindings (a.substitute substitution) (b.substitute substitution)
      (arguments.map (Term.substitute substitution))
  | .effect id arguments => .effect id (arguments.map (Term.substitute substitution))
  | .row instances tails => .row (instances.map (Term.substitute substitution)) (tails.map (Term.substitute substitution))
  | .projection trait member owners items kind => .projection trait member
      (owners.map (Term.substitute substitution)) (items.map (Term.substitute substitution)) kind
  | .constantTuple fields => .constantTuple (fields.map (Term.substitute substitution))
  | .constantConstructor id arguments fields => .constantConstructor id
      (arguments.map (Term.substitute substitution)) (fields.map (Term.substitute substitution))
  | term => term

def Constraint.substitute (substitution : Substitution) : Constraint → Constraint
  | .equal a b => .equal (a.substitute substitution) (b.substitute substitution)
  | .outlives a b => .outlives (a.substitute substitution) (b.substitute substitution)
  | .typeOutlives a b => .typeOutlives (a.substitute substitution) (b.substitute substitution)
  | .rowIncludes a b => .rowIncludes (a.substitute substitution) (b.substitute substitution)
  | .implements trait arguments negative => .implements trait (arguments.map (Term.substitute substitution)) negative
  | .use type quantity => .use (type.substitute substitution) quantity
  | .callable receiver arguments output effects unsafe => .callable (receiver.substitute substitution)
      (arguments.map (Term.substitute substitution)) (output.substitute substitution) (effects.substitute substitution) unsafe
  | .runsIn receiver access arguments after unsafe => .runsIn (receiver.substitute substitution)
      (access.substitute substitution) (arguments.map (Term.substitute substitution)) (after.substitute substitution) unsafe
  | .quantified binders requirements => .quantified binders
      (requirements.map (Constraint.substitute (substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1))))))

def Signature.instantiate (signature : Signature) (substitution : Substitution) : Signature :=
  { signature with
    generics := []
    parameters := signature.parameters.map (Term.substitute substitution)
    result := signature.result.substitute substitution
    effects := signature.effects.substitute substitution
    constraints := signature.constraints.map (Constraint.substitute substitution) }

namespace Kernel

def Local.mapTerms (f : Term → Term) (local : Local) : Local := { local with type := f local.type }
def Capture.mapTerms (f : Term → Term) (capture : Capture) : Capture := { capture with type := f capture.type }

def Pattern.mapTerms (f : Term → Term) : Pattern → Pattern
  | .bind local => .bind (local.mapTerms f)
  | .tuple fields => .tuple (fields.map (Pattern.mapTerms f))
  | .array fields => .array (fields.map (Pattern.mapTerms f))
  | .constructor id fields => .constructor id (fields.map (Pattern.mapTerms f))
  | .reference mode pattern => .reference mode (pattern.mapTerms f)
  | pattern => pattern

def Atom.mapTerms (f : Term → Term) : Atom → Atom
  | .constant value => .constant (f value)
  | .construct type variant fields => .construct (f type) variant fields
  | .closure id arguments captures => .closure id (arguments.map f) (captures.map (Capture.mapTerms f))
  | .function id arguments => .function id (arguments.map f)
  | .operation id family item => .operation id (family.map f) (item.map f)
  | .primitive id arguments operands => .primitive id (arguments.map f) operands
  | atom => atom

def Invocation.instantiate (call : Invocation) (substitution : Substitution) : Invocation :=
  { call with signature := call.signature.instantiate substitution }

mutual
  def Code.instantiate (substitution : Substitution) : Code → Code
    | .result value => .result value
    | .bind local value next => .bind (local.mapTerms (Term.substitute substitution))
        (value.mapTerms (Term.substitute substitution)) (next.instantiate substitution)
    | .evaluate local value next => .evaluate (local.mapTerms (Term.substitute substitution))
        (value.instantiate substitution) (next.instantiate substitution)
    | .assign destination value next => .assign destination value (next.instantiate substitution)
    | .discard value next => .discard value (next.instantiate substitution)
    | .invoke local call next => .invoke (local.mapTerms (Term.substitute substitution))
        (call.instantiate substitution) (next.instantiate substitution)
    | .tail call => .tail (call.instantiate substitution)
    | .scope id body => .scope id (body.instantiate substitution)
    | .label brand region result body => .label brand region (result.substitute substitution) (body.instantiate substitution)
    | .choose subject arms => .choose subject (arms.map (Arm.instantiate substitution))
    | .handle id computation handler => .handle id (computation.instantiate substitution) (handler.instantiate substitution)
    | .test local subject pattern id next => .test (local.mapTerms (Term.substitute substitution)) subject
        (pattern.mapTerms (Term.substitute substitution)) id (next.instantiate substitution)
    | .endLoan handle next => .endLoan handle (next.instantiate substitution)
    | .unsafeScope body => .unsafeScope (body.instantiate substitution)
    | .closeAvailable value next => .closeAvailable value (next.instantiate substitution)
    | .reserve local brand places next => .reserve (local.mapTerms (Term.substitute substitution)) brand places (next.instantiate substitution)
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

def Instance (program : Program) (id : DeclId) (arguments : List Term) (function : Function) : Prop :=
  ∃ template declaration substitution,
    program.function id = some template ∧ program.declarations.function id = some declaration ∧
    template.signature = declaration.signature ∧
    Instantiates template.signature.generics arguments substitution ∧
    ConstraintsHold program.declarations ⟨[],[],0,declaration.header.module,false⟩ substitution template.signature.constraints ∧
    function = template.instantiate substitution

end Kernel
end Glorious.Language
