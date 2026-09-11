import Glorious.Semantics.Patterns

namespace Glorious.Semantics

structure TypedSlot where
  id : Id
  type : Term
  mutable : Bool := false
  span : Span := {}
  deriving Repr

structure CallInput where
  position : InputPosition
  value : Place
  expected : Term
  deriving Repr

structure CallSite where
  identity : Id
  callee : Place
  inputs : List CallInput
  signature : Signature
  span : Span
  unsafePermission : Bool
  deriving Repr

structure PatternBinding where
  slot : TypedSlot
  projections : List Projection
  borrowed : Option (Mutability × Term)
  deriving Repr

inductive CoreOp where
  | declare (slot : TypedSlot)
  | constant (destination : Id) (value : Term)
  | literalView (destination : Id) (binding : DeclId) (bytes : List UInt8)
  | read (destination : Id) (source : Place) (forcedMove : Bool)
  | initializeOwner (destination : Place) (source : Place)
  | assign (destination source : Place)
  | construct (destination : Id) (constructor : Option DeclId) (fields : List Place)
  | closure (destination : Id) (function : DeclId) (arguments : List Term)
      (captures : List Capture) (materialized : Bool)
  | borrow (destination : Id) (mode : Mutability) (region : Term) (source : Place)
  | endLoan (identity : Id)
  | discard (source : Place)
  | invoke (destination : Id) (call : CallSite)
  | perform (destination : Id) (operation : DeclId) (arguments : List Term)
      (payload : List Place) (signature : Signature)
  | deconstruct (source : Place) (pattern : CheckedPattern)
      (bindings : List PatternBinding)
  | test (destination : Id) (source : Place) (pattern : CheckedPattern)
      (positiveBrand negativeBrand : Term)
  | machine (destination : Id) (binding : DeclId) (arguments : List Place)
      (signature : Signature) (unsafePermission : Bool)
  | seal (values : List Place)
  deriving Repr

mutual
  inductive Core where
    | result (value : Place)
    | step (operation : CoreOp) (next : Core)
    | bind (destination : TypedSlot) (computation : Core) (next : Core)
    | scopeBlock (scope : Id) (body : Core)
    | cases (subject : Place) (clauses : List CoreCase)
    | label (identity : Id) (brand region resultType : Term) (body : Core)
    | handle (identity : Id) (body : Core) (clauses : List CoreHandler)
    | tail (call : CallSite)
    | leave (brand : Term) (payload : Place)
    | fatal (reason : Fatal)
    deriving Repr

  inductive CoreCase where
    | clause (pattern : CheckedPattern) (bindings : List PatternBinding) (body : Core)
    deriving Repr

  inductive CoreHandler where
    | completion (pattern : CheckedPattern) (bindings : List PatternBinding) (body : Core)
    | operation (operation : DeclId) (effectInstance : List Term) (patterns : List CheckedPattern)
        (bindings : List PatternBinding) (continuation : Option TypedSlot)
        (policy : Option ResumptionPolicy) (body : Core)
    deriving Repr
end

structure CoreFunction where
  declaration : DeclId
  signature : Signature
  parameters : List TypedSlot
  captures : List Capture
  receiver : ReceiverMode
  body : Core
  namedExit : Option Term
  span : Span
  deriving Repr

structure CoreProgram where
  source : Program
  functions : List CoreFunction
  bindings : List Binding
  inference : Inference
  deriving Repr

def CoreProgram.function (program : CoreProgram) (declaration : DeclId) : Option CoreFunction :=
  program.functions.find? (fun f => f.declaration == declaration)

def coreStepList (operations : List CoreOp) (next : Core) : Core :=
  operations.foldr Core.step next

inductive Guard where
  | constructor (origin : Id) (declaration : DeclId) (positive : Bool)
  | scalar (origin : Id) (value : ScalarValue) (positive : Bool)
  | invocation (origin : Id) (branch : Nat)
  deriving BEq, DecidableEq, Repr

def incompatibleGuards (a b : Guard) : Bool :=
  match a, b with
  | .constructor x c p, .constructor y d q => x == y &&
      ((c == d && p != q) || (p && q && c != d))
  | .scalar x c p, .scalar y d q => x == y &&
      ((c == d && p != q) || (p && q && c != d))
  | .invocation x a, .invocation y b => x == y && a != b
  | _, _ => false

def consistentGuards (guards : List Guard) : Bool :=
  !(guards.any (fun a => guards.any (incompatibleGuards a)))

end Glorious.Semantics
