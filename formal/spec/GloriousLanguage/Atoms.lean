import GloriousLanguage.Machine

/-! Atomic construction, acquisition and borrowing. Machine/host leaves are
dispatched by manifest identity and are interpreted in `Memory`/`Primitives`.
They are not inferred from library function spelling. -/
namespace Glorious.Language.Execution

open Kernel

mutual
  inductive ConstantValue (program : Language.Program) (context : Language.Context) :
      Nat → Term → Nat → Value → Prop where
    | scalar {next scalar} : scalar.Valid program.input.target →
        ConstantValue program context next (.constant scalar) (next+1)
          (.resident next (.scalar scalar.type) (.scalar scalar) true [])
    | unit {next} : ConstantValue program context next (.constantTuple []) (next+1)
        (.resident next .unit .unit true [])
    | tuple {next fields finish residents} : fields ≠ [] → ConstantValues program context (next+1) fields finish residents →
        ConstantValue program context next (.constantTuple fields) finish
          (.resident next (.tuple (residents.map Value.type)) .tuple true (residents.map some))
    | constructor {next id arguments fields finish residents type} :
        ConstantType program context (.constantConstructor id arguments fields) type →
        ConstantValues program context (next+1) fields finish residents →
        ConstantValue program context next (.constantConstructor id arguments fields) finish
          (.resident next type (.constructor id) true (residents.map some))

  inductive ConstantValues (program : Language.Program) (context : Language.Context) :
      Nat → List Term → Nat → List Value → Prop where
    | nil {next} : ConstantValues program context next [] next []
    | cons {next first rest middle finish value values} : ConstantValue program context next first middle value →
        ConstantValues program context middle rest finish values →
        ConstantValues program context next (first :: rest) finish (value :: values)
end

inductive Captures (program : Kernel.Program) (context : Context) :
    World → List Capture → List Address → World → Prop where
  | nil {world} : Captures program context world [] [] world
  | owned {before capture rest source authority destination allocated middle after addresses} : capture.mode = .own →
      ResolvesPlace before context.environment capture.place source authority →
      Temporary program context capture.type before destination allocated →
      Acquires program.declarations allocated authority false source destination middle →
      Captures program context middle rest addresses after →
      Captures program context before (capture :: rest) (destination :: addresses) after
  | borrowed {before capture rest source authority destination allocated middle after addresses mode} :
      (capture.mode = .shared ∧ mode = .shared ∨ capture.mode = .unique ∧ mode = .unique) →
      ResolvesPlace before context.environment capture.place source authority →
      Temporary program context capture.type before destination allocated →
      Borrows program.declarations allocated authority mode context.region source destination middle →
      Captures program context middle rest addresses after →
      Captures program context before (capture :: rest) (destination :: addresses) after

def ConstructorHead (program : Language.Program) (type : Term) (variant : Option DeclId)
    (fieldTypes : List Term) (head : ValueHead) : Prop :=
  (type = .tuple fieldTypes ∧ variant = none ∧ head = .tuple) ∨
  (∃ element sign width length, type = .array element (.constant (.integer sign width length)) ∧
    variant = none ∧ head = .array ∧ length = fieldTypes.length ∧ ∀ field ∈ fieldTypes, field = element) ∨
  (∃ id arguments data constructor substitution,
    type = .nominal data.header.id arguments ∧ variant = some id ∧ head = .constructor id ∧
    program.Constructor id data constructor ∧ Instantiates data.generics arguments substitution ∧
    ListRel (Substitutes substitution) (constructor.fields.map (·.type)) fieldTypes)

def DestinationType (world : World) (address : Address) (type : Term) : Prop :=
  address.fields = [] ∧ ∃ root, world.root address = some root ∧ root.type = type ∧ root.value = none

inductive AtomStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | constant {before context destination term next value finish after} :
      before.task = .atom context destination (.constant term) next →
      ConstantValue program.declarations context.static before.world.nextOwner term finish value →
      DestinationType before.world destination value.type → before.world.write destination (some value) = some after →
      AtomStep program before none { before with world := { after with nextOwner := finish }, task := .run context next }
  | acquire {before context destination place force next source authority after} :
      before.task = .atom context destination (.acquire place force) next →
      ResolvesPlace before.world context.environment place source authority →
      Acquires program.declarations before.world authority force source destination after →
      AtomStep program before (some (if force then .move source destination else
        if (after.read source).isSome then .copy source destination else .move source destination))
        { before with world := after, task := .run context next }
  | borrow {before context destination place mode lexicalRegion next source authority after} :
      before.task = .atom context destination (.borrow place mode lexicalRegion) next →
      ResolvesPlace before.world context.environment place source authority →
      Borrows program.declarations before.world authority mode context.region source destination after →
      AtomStep program before (some (.borrow source before.world.nextLoan))
        { before with world := after, task := .run context next }
  | construct {before context destination type variant fields next sources residents head after} :
      before.task = .atom context destination (.construct type variant fields) next →
      Addresses before.world context.environment fields sources → ListRel (World.Stores before.world) sources residents →
      ConstructorHead program.declarations type variant (residents.map Value.type) head →
      DestinationType before.world destination type → NewValue program.declarations before.world destination type head sources after →
      AtomStep program before none { before with world := after, task := .run context next }
  | closure {before context destination id arguments captures next sources captured after function} :
      before.task = .atom context destination (.closure id arguments captures) next → Instance program id arguments function →
      Captures program context before.world captures sources captured →
      ListRel (fun formal address => ∃ value, captured.Stores address value ∧ value.type = formal.type) function.captures sources →
      DestinationType captured destination (.callable id arguments) →
      NewValue program.declarations captured destination (.callable id arguments) (.callable id arguments) sources after →
      AtomStep program before none { before with world := after, task := sources.foldr (fun address nextTask => .retire address.root nextTask) (.run context next) }
  | function {before context destination id arguments next function after} :
      before.task = .atom context destination (.function id arguments) next → Instance program id arguments function →
      function.captures = [] → DestinationType before.world destination (.callable id arguments) →
      NewValue program.declarations before.world destination (.callable id arguments) (.callable id arguments) [] after →
      AtomStep program before none { before with world := after, task := .run context next }
  | operation {before context destination id family item next operation after} :
      before.task = .atom context destination (.operation id family item) next →
      program.declarations.operation id = some operation →
      NewValue program.declarations before.world destination (.callable id (family ++ item)) (.operation id (family ++ item)) [] after →
      AtomStep program before none { before with world := after, task := .run context next }
  | label {before context destination lexical next brand root after} :
      before.task = .atom context destination (.label lexical) next → context.labels.get lexical = some brand →
      before.world.root destination = some root →
      (∃ region result, root.type = .label (.rigid brand .brand 0) region result) →
      NewValue program.declarations before.world destination root.type (.label brand) [] after →
      AtomStep program before none { before with world := after, task := .run context next }
  | primitive {before context destination id arguments operands next binding addresses} :
      before.task = .atom context destination (.primitive id arguments operands) next →
      binding ∈ program.declarations.input.manifest.bindings → binding.declaration = id →
      Addresses before.world context.environment operands addresses →
      (binding.signature.unsafeAllowed = true → context.unsafeAllowed = true) →
      AtomStep program before none { before with task := .primitive context destination binding arguments addresses next }

end Glorious.Language.Execution
