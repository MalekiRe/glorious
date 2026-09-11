import GloriousLanguage.SourceRules
import GloriousLanguage.Contracts

/-! Declarative, bidirectional source elaboration. Existential choices are
constraints to discharge, not permission to guess unresolved evidence. The
admission predicate checks the complete package closure and all generated
functions before any source execution is defined. -/
namespace Glorious.Language.Elaboration

open Kernel

structure LocalName where
  name : String
  place : Place
  type : Term
  mutable : Bool
  deriving Repr, Inhabited

structure Context where
  typed : Typing.Context
  names : List LocalName := []
  namedLabels : List (String × Identity) := []
  contextual : List Signature := []
  origin : SourceAnchor
  owner : Option DeclId := none
  capturePlaces : List (Source.Expr × Local) := []
  visibility : Visibility := .privateScope
  attributes : List Source.Attribute := []
  selfType : Option Term := none
  itemIndex : Nat := 0
  deriving Repr, Inhabited

def Context.bind (context : Context) (name : String) (localSlot : Local) : Context :=
  { context with typed := context.typed.bind localSlot, names := ⟨name,⟨localSlot.id,[]⟩,localSlot.type,localSlot.mutable⟩ :: context.names.filter (fun old => old.name != name) }

def Context.child (context : Context) (index : Nat) : Context :=
  { context with origin := { context.origin with node := context.origin.node ++ [index] }, itemIndex := 0 }

def Fresh (context : Context) (localSlot : Local) : Prop := ∀ old ∈ context.typed.locals, old.id ≠ localSlot.id

def ScalarName : String → Scalar → Prop
  | "char", scalar => scalar = .character
  | "f32", scalar => scalar = .floating .single
  | "f64", scalar => scalar = .floating .double
  | name, scalar => ∃ suffix, suffix = some scalar ∧ Source.IntegerSuffix suffix (Source.text name)

def BuiltinType (program : Language.Program) (context : Language.Context) (name : String) (type : Term) : Prop :=
  (∀ header, ¬ Qualified program context.module .type [name] header) ∧
    ∃ scalar, ScalarName name scalar ∧ type = .scalar scalar

inductive LiteralConstant (target : TargetProfile) : Source.Literal → Option Term → Term → Term → Prop where
  | integer {literal sign width} : literal.suffix = some (.integer sign width) →
      IntegerRange target sign width (Source.digitsValue literal.base literal.digits) →
      LiteralConstant target (.integer literal) none (.constant (.integer sign width (Source.digitsValue literal.base literal.digits))) (.scalar (.integer sign width))
  | constrainedInteger {literal sign width} : (literal.suffix = none ∨ literal.suffix = some (.integer sign width)) →
      IntegerRange target sign width (Source.digitsValue literal.base literal.digits) →
      LiteralConstant target (.integer literal) (some (.scalar (.integer sign width)))
        (.constant (.integer sign width (Source.digitsValue literal.base literal.digits))) (.scalar (.integer sign width))
  | defaultInteger {literal} : literal.suffix = none →
      IntegerRange target true (.fixed 64) (Source.digitsValue literal.base literal.digits) →
      LiteralConstant target (.integer literal) none
        (.constant (.integer true (.fixed 64) (Source.digitsValue literal.base literal.digits))) (.scalar (.integer true (.fixed 64)))
  | floating {literal width bits expected} :
      ((expected = some (.scalar (.floating width)) ∧ (literal.width = none ∨ literal.width = some width)) ∨
        (expected = none ∧ literal.width.getD .double = width)) →
      RoundsFinite width (decimalFraction literal) false bits →
      LiteralConstant target (.floating literal) expected (.constant (.floating width bits)) (.scalar (.floating width))
  | character {value expected} : Source.UnicodeScalar value → (expected = none ∨ expected = some (.scalar .character)) →
      LiteralConstant target (.character value) expected (.constant (.character value)) (.scalar .character)
  | byte {value expected} : value < 256 → (expected = none ∨ expected = some (.scalar (.integer false (.fixed 8)))) →
      LiteralConstant target (.byte value) expected (.constant (.integer false (.fixed 8) value)) (.scalar (.integer false (.fixed 8)))

mutual
  inductive TypeExpression (program : Kernel.Program) (context : Context) : Source.TypeExpr → Kind → Term → Prop where
    | self {type} : context.selfType = some type → TypeExpression program context (.path ["Self"] [] []) .type type
    | infer {kind cell} : TypeExpression program context .infer kind (.variable cell kind context.typed.static.universeLevel)
    | unit : TypeExpression program context .unit .type .unit
    | bottom : TypeExpression program context .bottom .type .bottom
    | builtin {name type} : BuiltinType program.declarations context.typed.static name type →
        TypeExpression program context (.path [name] [] []) .type type
    | parameter {name binder} : binder ∈ context.typed.static.binders → binder.name = name →
        TypeExpression program context (.path [name] [] []) binder.kind (.parameter binder.id binder.kind)
    | lifetime {name binder} : binder ∈ context.typed.static.binders → binder.name = name → binder.kind = .region →
        TypeExpression program context (.lifetime name) .region (.parameter binder.id .region)
    | static : TypeExpression program context (.lifetime "static") .region .staticRegion
    | inferredRegion {cell} : TypeExpression program context (.lifetime "_") .region (.variable cell .region context.typed.static.universeLevel)
    | tuple {fields types} : TypeExpressions program context fields (List.replicate fields.length .type) types →
        TypeExpression program context (.tuple fields) .type (.tuple types)
    | array {element length type size} : TypeExpression program context element .type type → TypeExpression program context length .constant size →
        TypeExpression program context (.array element length) .type (.array type size)
    | reference {mode sourceRegion sourceType region type} :
        TypeExpression program context (.lifetime (sourceRegion.getD "_")) .region region → TypeExpression program context sourceType .type type →
        TypeExpression program context (.reference mode sourceRegion sourceType) .type (.reference mode region type)
    | pointer {mode sourceType type} : TypeExpression program context sourceType .type type →
        TypeExpression program context (.pointer mode sourceType) .type (.rawPointer mode type)
    | nominal {path sourceArguments header data arguments} : Qualified program.declarations context.typed.static.module .type path header →
        program.declarations.data header.id = some data →
        TypeExpressions program context sourceArguments (data.generics.map (·.kind)) arguments →
        TypeExpression program context (.path path sourceArguments []) .type (.nominal data.header.id arguments)
    | alias {path sourceArguments header alias arguments} : Qualified program.declarations context.typed.static.module .type path header →
        program.declarations.alias header.id = some alias → TypeExpressions program context sourceArguments (alias.generics.map (·.kind)) arguments →
        TypeExpression program context (.path path sourceArguments []) .type (.alias alias.header.id arguments)
    | effect {path sourceArguments header effect arguments} : Qualified program.declarations context.typed.static.module .effect path header →
        program.declarations.effect header.id = some effect → TypeExpressions program context sourceArguments (effect.generics.map (·.kind)) arguments →
        TypeExpression program context (.path path sourceArguments []) .effect (.effect effect.header.id arguments)
    | constant {literal value type} : LiteralConstant program.declarations.input.target literal none value type →
        TypeExpression program context (.constant literal) .constant value
    | quantity {value} : TypeExpression program context (.quantity value) .quantity (.quantity value)
    | row {sourceInstances sourceTails instances tails} :
        TypeExpressions program context sourceInstances (List.replicate sourceInstances.length .effect) instances →
        TypeExpressions program context sourceTails (List.replicate sourceTails.length .row) tails →
        TypeExpression program context (.row sourceInstances sourceTails) .row (.row instances tails)
    | associated {sourceOwner traitPath sourceTraitArguments member sourceArguments owner traitHeader trait associated owners arguments} :
        TypeExpression program context sourceOwner .type owner →
        Qualified program.declarations context.typed.static.module .trait traitPath traitHeader →
        program.declarations.trait traitHeader.id = some trait → program.declarations.associated associated.header.id = some associated →
        associated.owner = trait.header.id → associated.header.name = member →
        TypeExpressions program context sourceTraitArguments (trait.generics.drop 1 |>.map (·.kind)) owners →
        TypeExpressions program context sourceArguments (associated.generics.map (·.kind)) arguments →
        Entails program.declarations context.typed.static (.implements trait.header.id (owner :: owners) false) →
        TypeExpression program context (.associated sourceOwner traitPath sourceTraitArguments member sourceArguments) associated.kind
          (.projection trait.header.id associated.header.id (owner :: owners) arguments associated.kind)
    | constructor {path sourceArguments sourceFields header data variant arguments fields types substitution} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.Constructor header.id data variant →
        TypeExpressions program context sourceArguments (data.generics.map (·.kind)) arguments → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        TypeExpressions program context sourceFields (List.replicate sourceFields.length .constant) fields →
        ListRel (ConstantType program.declarations context.typed.static) fields types →
        TypeExpression program context (.constructor path sourceArguments sourceFields) .constant (.constantConstructor header.id arguments fields)

  inductive TypeExpressions (program : Kernel.Program) (context : Context) : List Source.TypeExpr → List Kind → List Term → Prop where
    | nil : TypeExpressions program context [] [] []
    | cons {first rest kind kinds term terms} : TypeExpression program context first kind term → TypeExpressions program context rest kinds terms →
        TypeExpressions program context (first :: rest) (kind :: kinds) (term :: terms)
end

def FieldIndex (program : Language.Program) (context : Language.Context) (type : Term) (name : String) (index : Nat) (fieldType : Term) : Prop :=
  (name = toString index ∧ Typing.FieldType program context type index fieldType true) ∨
  ∃ id arguments data variant field substitution,
    type = .nominal id arguments ∧ program.data id = some data ∧ data.isEnum = false ∧ data.variants = [variant] ∧
    variant.fields[index]? = some field ∧ field.header.name = name ∧ Visible field.header context.module ∧
    Instantiates data.generics arguments substitution ∧ Substitutes substitution field.type fieldType

inductive PlaceExpression (program : Kernel.Program) (context : Context) : Source.Expr → Place → Term → Bool → Prop where
  | captured {source localSlot} : (source,localSlot) ∈ context.capturePlaces →
      PlaceExpression program context source ⟨localSlot.id,[]⟩ localSlot.type localSlot.mutable
  | name {name binding} : binding ∈ context.names → binding.name = name →
      (∀ other ∈ context.names, other.name = name → other = binding) →
      PlaceExpression program context (.name [name] [] []) binding.place binding.type binding.mutable
  | project {source name place type mutable index field} : PlaceExpression program context source place type mutable →
      FieldIndex program.declarations context.typed.static type name index field →
      PlaceExpression program context (.project source name) { place with projections := place.projections ++ [.field index] } field mutable
  | dereference {source place mode region type mutable} : PlaceExpression program context source place (.reference mode region type) mutable →
      PlaceExpression program context (.dereference source) { place with projections := place.projections ++ [.dereference] } type (mode == .unique)

def ConstantAlias (program : Kernel.Program) (context : Context) (path : Source.Path)
    (sourceArguments : List Source.TypeExpr) (value type : Term) : Prop :=
  ∃ header constant arguments substitution,
    Qualified program.declarations context.typed.static.module .value path header ∧ program.declarations.constant header.id = some constant ∧
    TypeExpressions program context sourceArguments (constant.generics.map (·.kind)) arguments ∧
    Instantiates constant.generics arguments substitution ∧ Substitutes substitution constant.value value ∧ Substitutes substitution constant.type type

def ConstructorName (program : Kernel.Program) (context : Context) (path : Source.Path) : Prop :=
  ∃ header data variant, Qualified program.declarations context.typed.static.module .value path header ∧
    program.declarations.Constructor header.id data variant

inductive ConstantPattern : Term → Pattern → Prop where
  | scalar {value} : (∀ width bits, value ≠ .floating width bits) → ConstantPattern (.constant value) (.scalar value)
  | unit : ConstantPattern (.constantTuple []) .unit
  | tuple {values patterns} : ListRel ConstantPattern values patterns → ConstantPattern (.constantTuple values) (.tuple patterns)
  | constructor {id arguments values patterns} : ListRel ConstantPattern values patterns →
      ConstantPattern (.constantConstructor id arguments values) (.constructor id patterns)

def ExpandRemainder (fields : List Source.Pattern) (remainder : Option Nat) (arity : Nat) (expanded : List Source.Pattern) : Prop :=
  (remainder = none ∧ expanded = fields ∧ fields.length = arity) ∨
  ∃ index, remainder = some index ∧ index ≤ fields.length ∧ fields.length ≤ arity ∧
    expanded = fields.take index ++ List.replicate (arity-fields.length) .wildcard ++ fields.drop index

mutual
  inductive PatternExpression (program : Kernel.Program) (context : Context) :
      Source.Pattern → Term → Access → Pattern → List (String × Local) → Prop where
    | wildcard {type access} : PatternExpression program context .wildcard type access .wildcard []
    | binder {name explicit type access localSlot} : Fresh context localSlot →
        (explicit = true ∨ (¬ ConstructorName program context [name] ∧ ∀ value result, ¬ ConstantAlias program context [name] [] value result)) →
        (localSlot.type = type ∧ access = .owned ∨ ∃ region mode, localSlot.type = .reference mode region type ∧
          access = if mode = .shared then .shared else .unique) →
        PatternExpression program context (.binder name explicit) type access (.bind localSlot) [(name,localSlot)]
    | constant {path sourceArguments value type pattern access} : ConstantAlias program context path sourceArguments value type →
        ConstantPattern value pattern → PatternExpression program context (.constant path sourceArguments) type access pattern []
    | bareConstant {name value type pattern access} : ConstantAlias program context [name] [] value type → ConstantPattern value pattern →
        PatternExpression program context (.binder name false) type access pattern []
    | literal {literal type value pattern access} : LiteralConstant program.declarations.input.target literal (some type) value type →
        ConstantPattern value pattern → PatternExpression program context (.literal literal) type access pattern []
    | tuple {fields remainder types expanded patterns bindings access} : ExpandRemainder fields remainder types.length expanded →
        PatternExpressions program context expanded types access patterns bindings →
        PatternExpression program context (.tuple fields remainder) (.tuple types) access (.tuple patterns) bindings
    | array {fields remainder type sign width count expanded patterns bindings access} : 0 ≤ count →
        ExpandRemainder fields remainder count.toNat expanded →
        PatternExpressions program context expanded (List.replicate count.toNat type) access patterns bindings →
        PatternExpression program context (.array fields remainder) (.array type (.constant (.integer sign width count))) access (.array patterns) bindings
    | constructor {path sourceArguments fields remainder header data variant arguments substitution types expanded patterns bindings access} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.Constructor header.id data variant →
        TypeExpressions program context sourceArguments (data.generics.map (·.kind)) arguments → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types → ExpandRemainder fields remainder types.length expanded →
        PatternExpressions program context expanded types access patterns bindings →
        Typing.PatternType program.declarations context.typed.static (.constructor header.id patterns) (.nominal data.header.id arguments) access (bindings.map Prod.snd) →
        PatternExpression program context (.constructor path sourceArguments fields remainder) (.nominal data.header.id arguments) access
          (.constructor header.id patterns) bindings
    | reference {mode source region type pattern bindings access} :
        PatternExpression program context source type (if mode = .shared then .shared else .unique) pattern bindings →
        PatternExpression program context (.reference mode source) (.reference mode region type) access (.reference mode pattern) bindings
    | record {path sourceArguments fields remainder header data variant arguments substitution types ordered patterns bindings access} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.Constructor header.id data variant →
        TypeExpressions program context sourceArguments (data.generics.map (·.kind)) arguments → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types → (fields.map Prod.fst).Nodup →
        ordered.length = variant.fields.length →
        (∀ index field, variant.fields[index]? = some field →
          ((∃ pattern, (field.header.name,pattern) ∈ fields ∧ ordered[index]? = some pattern ∧ Visible field.header context.typed.static.module) ∨
            (remainder = true ∧ (∀ pattern, (field.header.name,pattern) ∉ fields) ∧ ordered[index]? = some .wildcard))) →
        (∀ name pattern, (name,pattern) ∈ fields → ∃ field ∈ variant.fields, field.header.name = name) →
        PatternExpressions program context ordered types access patterns bindings →
        Typing.PatternType program.declarations context.typed.static (.constructor header.id patterns) (.nominal data.header.id arguments) access (bindings.map Prod.snd) →
        PatternExpression program context (.record path sourceArguments fields remainder) (.nominal data.header.id arguments) access
          (.constructor header.id patterns) bindings

  inductive PatternExpressions (program : Kernel.Program) (context : Context) :
      List Source.Pattern → List Term → Access → List Pattern → List (String × Local) → Prop where
    | nil {access} : PatternExpressions program context [] [] access [] []
    | cons {first rest type types access pattern patterns bindings more} : PatternExpression program context first type access pattern bindings →
        PatternExpressions program context rest types access patterns more →
        (∀ name localSlot, (name,localSlot) ∈ bindings → ∀ other, (name,other) ∉ more) →
        PatternExpressions program context (first :: rest) (type :: types) access (pattern :: patterns) (bindings ++ more)
end

def BindNames (context : Context) (bindings : List (String × Local)) : Context :=
  bindings.foldl (fun current (name,localSlot) => current.bind name localSlot) context

structure BindingCode where
  localSlot : Local
  value : Code
  deriving Repr, Inhabited

def sequence (bindings : List BindingCode) (next : Code) : Code :=
  bindings.foldr (fun binding rest => .evaluate binding.localSlot binding.value rest) next

def AtomCode (localSlot : Local) (atom : Atom) : Code := .bind localSlot atom (.result ⟨localSlot.id,[]⟩)

def SignatureReceiver (program : Kernel.Program) (context : Context) (type : Term)
    (access : Access) (signature : Signature) : Prop :=
  (∃ id arguments, type = .callable id arguments ∧ Typing.CallSignature program.declarations context.typed.static id arguments signature) ∨
  (∃ brand argument answer effects quantity, type = .continuation brand argument answer effects quantity ∧
    signature.parameters = [argument] ∧ signature.result = answer ∧ signature.effects = effects) ∨
  (∃ brand region result, type = .label brand region result ∧ signature.parameters = [result] ∧
    signature.result = .bottom ∧ signature.effects = .row [] []) ∨
  (∃ mode region inner, type = .reference mode region inner ∧
    Entails program.declarations context.typed.static (.callable type signature.parameters signature.result signature.effects signature.unsafeAllowed) ∧
    (mode = .shared → access = .shared))

def IsContextual (program : Kernel.Program) (context : Context) (type : Term) (signature : Signature) : Prop :=
  Entails program.declarations context.typed.static
    (.callable type signature.parameters signature.result signature.effects signature.unsafeAllowed)

def FixitySelected (program : Language.Program) (module : ModuleId) (operator : String) (prefixForm : Bool) (fixity : FixityDefinition) : Prop :=
  Definition.fixity fixity ∈ program.declarations ∧ fixity.header.module = module ∧ fixity.operator = operator ∧
  ((prefixForm = true ∧ fixity.kind = .prefixForm) ∨ (prefixForm = false ∧ fixity.kind ≠ .prefixForm)) ∧
  ∀ other, Definition.fixity other ∈ program.declarations → other.header.module = module → other.operator = operator →
    ((other.kind = .prefixForm) ↔ (fixity.kind = .prefixForm)) → other.target = fixity.target ∧ other.precedence = fixity.precedence ∧ other.kind = fixity.kind

inductive Grouped (program : Language.Program) (module : ModuleId) : Source.Expr → List (String × Source.Expr) → Source.Expr → Prop where
  | atom {expression} : Grouped program module expression [] expression
  | split {first left operator right rest lhs rhs fixity path} :
      FixitySelected program module operator false fixity →
      (∀ op operand, (op,operand) ∈ left ++ rest → ∃ other, FixitySelected program module op false other ∧ fixity.precedence ≤ other.precedence) →
      (∀ op operand, (op,operand) ∈ left → ∀ other, FixitySelected program module op false other →
        other.precedence = fixity.precedence → fixity.kind = .left ∧ other.kind = .left) →
      (∀ op operand, (op,operand) ∈ rest → ∀ other, FixitySelected program module op false other →
        other.precedence = fixity.precedence → fixity.kind = .right ∧ other.kind = .right) →
      Grouped program module first left lhs → Grouped program module right rest rhs →
      (∃ header, Qualified program module .value path header ∧ header.id = fixity.target) →
      Grouped program module first (left ++ (operator,right) :: rest) (.call (.name path [] []) [lhs,rhs])

def CaptureAccess : CaptureMode → Access | .shared => .shared | .unique => .unique | .own => .owned
def CaptureRank : CaptureMode → Nat | .shared => 0 | .unique => 1 | .own => 2

def CapturesResolved (program : Kernel.Program) (context : Context) (sources : List Source.Expr)
    (captures : List Capture) (formals : List Local) : Prop :=
  ListRel (fun source capture => ∃ type mutable,
    PlaceExpression program context source capture.place type mutable ∧
    (capture.mode = .unique → mutable = true) ∧
    (capture.mode = .own → capture.type = type) ∧
    (capture.mode ≠ .own → ∃ region, capture.type = .reference
      (if capture.mode = .shared then .shared else .unique) region type)) sources captures ∧
  ListRel (fun capture formal => capture.formal = formal.id ∧ capture.type = formal.type) captures formals ∧
  (captures.map (·.formal)).Nodup

def ExtendsWithCaptures (outer inner : Context) (sources : List Source.Expr) (captures : List Local) : Prop :=
  inner.capturePlaces = sources.zip captures ∧ inner.typed.static.module = outer.typed.static.module ∧
  inner.typed.static.unsafeAllowed = false ∧ inner.namedLabels = outer.namedLabels

inductive SourceItemName : Source.Declaration → String → Namespace → Prop where
  | trait {name generics requirements members unsafeAllowed} : SourceItemName (.trait name generics requirements members unsafeAllowed) name .trait
  | effect {name generics requirements operations} : SourceItemName (.effect name generics requirements operations) name .effect
  | associated {name generics kind requirements value} : SourceItemName (.associated name generics kind requirements value) name .type
  | constant {name generics type value} : SourceItemName (.constant name generics type value) name .value
  | global {name type value} : SourceItemName (.global name type value) name .value
  | module {name members} : SourceItemName (.module name members) name .type
  | import {tree name} : SourceItemName (.import tree) name .value
  | fixity {kind precedence operator target} : SourceItemName (.fixity kind precedence operator target) operator .value
  | implementation {generics trait self requirements members unsafeAllowed negative name} :
      SourceItemName (.implementation generics trait self requirements members unsafeAllowed negative) name .trait

def AttributeContract (attributes : List Source.Attribute) (definition : Definition) : Prop :=
  (∀ annotationEntry ∈ attributes, match annotationEntry with
    | .reprC => ∃ data, definition = .data data ∧ data.representation = .c
    | .transparent => ∃ data, definition = .data data ∧ data.representation = .transparent
    | .reprInteger sign width => ∃ data, definition = .data data ∧ data.representation = .integer sign width
    | .nonExhaustive => ∃ data, definition = .data data ∧ data.nonExhaustive = true
    | .exportName name => ∃ function, definition = .function function ∧ function.exportName = some name ∧ function.cABI = true
    | .noStd | .noPrelude => True
    | .metadata _ _ => False) ∧
  (∀ data, definition = .data data →
    (attributes.all (fun annotationEntry => match annotationEntry with | .reprC | .transparent | .reprInteger .. => false | _ => true) = true →
      data.representation = .glorious) ∧ (Source.Attribute.nonExhaustive ∉ attributes → data.nonExhaustive = false))

def MemberIdentities (program : Kernel.Program) (context : Context) (members : List Source.Declaration) (ids : List DeclId) : Prop :=
  ids.Nodup ∧ ids.length = members.length ∧
  ∀ id ∈ ids, ∃ declaration, program.declarations.lookup id = some declaration ∧
    (∃ member ∈ members, SourceItemName member declaration.header.name declaration.header.nameSpace) ∧
    declaration.header.module = context.typed.static.module

mutual
  inductive Expression (program : Kernel.Program) : Context → Source.Expr → Term → Code → Prop where
    | scalar {context literal type value localSlot} : LiteralConstant program.declarations.input.target literal (some type) value type →
        Fresh context localSlot → localSlot.type = type → Expression program context (.literal literal) type (AtomCode localSlot (.constant value))
    | defaultScalar {context literal type value localSlot} : LiteralConstant program.declarations.input.target literal none value type →
        Fresh context localSlot → localSlot.type = type → Expression program context (.literal literal) type (AtomCode localSlot (.constant value))
    | literalView {context literal scalars bytes primitive binding localSlot} :
        ((literal = .string scalars ∧ Source.Decodes bytes scalars ∧ primitive = .literalText) ∨
          (literal = .bytes bytes ∧ primitive = .literalBytes)) →
        binding ∈ program.declarations.input.manifest.bindings → binding.primitive = some primitive →
        Fresh context localSlot → localSlot.type = binding.signature.result →
        Expression program context (.literal literal) localSlot.type
          (AtomCode localSlot (.primitive binding.declaration [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) byte)))] []))
    | unit {context localSlot} : Fresh context localSlot → localSlot.type = .unit →
        Expression program context .unit .unit (AtomCode localSlot (.constant (.constantTuple [])))
    | localSlot {context source place type mutable localSlot} : PlaceExpression program context source place type mutable →
        Fresh context localSlot → localSlot.type = type → Expression program context source type (AtomCode localSlot (.acquire place false))
    | forcedMove {context source place type mutable localSlot} : PlaceExpression program context source place type mutable →
        Fresh context localSlot → localSlot.type = type → Expression program context (.move source) type (AtomCode localSlot (.acquire place true))
    | borrow {context source place type mutable localSlot mode region} : PlaceExpression program context source place type mutable →
        Fresh context localSlot → (mode = .unique → mutable = true) → localSlot.type = .reference mode (.rigid region .region 0) type →
        Expression program context (.borrow mode source) localSlot.type (AtomCode localSlot (.borrow place mode region))
    | constant {context path sourceArguments value type localSlot} : ConstantAlias program context path sourceArguments value type →
        Fresh context localSlot → localSlot.type = type → Expression program context (.name path sourceArguments []) type (AtomCode localSlot (.constant value))
    | function {context path sourceOwners sourceItems header declaration arguments signature localSlot} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.function header.id = some declaration →
        TypeExpressions program context (sourceOwners ++ sourceItems) (declaration.signature.generics.map (·.kind)) arguments →
        Typing.CallSignature program.declarations context.typed.static header.id arguments signature →
        Fresh context localSlot → localSlot.type = .callable header.id arguments →
        Expression program context (.name path sourceOwners sourceItems) localSlot.type (AtomCode localSlot (.function header.id arguments))
    | operation {context path sourceOwners sourceItems header operation arguments signature localSlot} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.operation header.id = some operation →
        TypeExpressions program context (sourceOwners ++ sourceItems) (operation.signature.generics.map (·.kind)) arguments →
        Typing.CallSignature program.declarations context.typed.static header.id arguments signature →
        Fresh context localSlot → localSlot.type = .callable header.id arguments →
        Expression program context (.name path sourceOwners sourceItems) localSlot.type (AtomCode localSlot (.operation header.id arguments []))
    | labelName {context name id region type localSlot} : (name,id) ∈ context.namedLabels → (id,region,type) ∈ context.typed.labels →
        Fresh context localSlot → localSlot.type = .label (.rigid id .brand 0) region type →
        Expression program context (.labelName name) localSlot.type (AtomCode localSlot (.label id))
    | tuple {context expressions types bindings places result} : Arguments program context expressions types bindings places →
        Fresh context result → result.type = .tuple types →
        Expression program context (.tuple expressions) result.type (sequence bindings (AtomCode result (.construct result.type none places)))
    | array {context expressions element bindings places result} :
        Arguments program context expressions (List.replicate expressions.length element) bindings places → Fresh context result →
        result.type = .array element (.constant (.integer false .pointer expressions.length)) →
        Expression program context (.array expressions) result.type (sequence bindings (AtomCode result (.construct result.type none places)))
    | constructor {context path sourceOwners sourceItems sources header data variant arguments substitution types bindings places result} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.Constructor header.id data variant →
        TypeExpressions program context (sourceOwners ++ sourceItems) (data.generics.map (·.kind)) arguments →
        Instantiates data.generics arguments substitution → ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        (∀ field ∈ variant.fields, Visible field.header context.typed.static.module) →
        Arguments program context sources types bindings places → Fresh context result → result.type = .nominal data.header.id arguments →
        Expression program context (.call (.name path sourceOwners sourceItems) sources) result.type
          (sequence bindings (AtomCode result (.construct result.type (some header.id) places)))
    | call {context source arguments callee calleeCode access signature bindings places result environment} :
        Fresh context callee → SignatureReceiver program context callee.type access signature →
        Expression program context source callee.type calleeCode →
        Arguments program { context with typed := context.typed.bind callee, contextual := signature :: context.contextual }
          arguments signature.parameters bindings places → Fresh context result → result.type = signature.result →
        Typing.InvocationType program.declarations context.typed ⟨⟨callee.id,[]⟩,places,access,environment,signature⟩ →
        Expression program context (.call source arguments) result.type
          (.evaluate callee calleeCode (sequence bindings (.invoke result ⟨⟨callee.id,[]⟩,places,access,environment,signature⟩ (.result ⟨result.id,[]⟩))))
    | tail {context source arguments callee calleeCode access signature bindings places result environment} :
        Fresh context callee → SignatureReceiver program context callee.type access signature → Expression program context source callee.type calleeCode →
        Arguments program { context with typed := context.typed.bind callee, contextual := signature :: context.contextual }
          arguments signature.parameters bindings places → Subtype program.declarations context.typed.static signature.result result →
        Expression program context (.tail source arguments) result
          (.evaluate callee calleeCode (sequence bindings (.tail ⟨⟨callee.id,[]⟩,places,access,environment,signature⟩)))
    | block {context statements result type code scope} : Block program context statements result type code →
        Expression program context (.block statements result) type (.scope scope code)
    | contextualBlock {context statements result expected signature function captures localSlot} :
        IsContextual program context expected signature →
        Closure program context (.block statements result) signature function captures → Fresh context localSlot → localSlot.type = expected →
        expected = .callable function.declaration [] →
        Expression program context (.block statements result) expected (AtomCode localSlot (.closure function.declaration [] captures))
    | anonymous {context head body signature function captures localSlot} :
        Head program context head signature → Closure program context (.function head body) signature function captures →
        Fresh context localSlot → localSlot.type = .callable function.declaration [] →
        Expression program context (.function head body) localSlot.type (AtomCode localSlot (.closure function.declaration [] captures))
    | clauses {context arms signature function captures localSlot} :
        Closure program context (.clauses arms) signature function captures → Fresh context localSlot → localSlot.type = .callable function.declaration [] →
        Expression program context (.clauses arms) localSlot.type (AtomCode localSlot (.closure function.declaration [] captures))
    | ownedCapture {context places source signature function captures localSlot} : Closure program context source signature function captures →
        (∀ source ∈ places, ∃ place type mutable capture,
          PlaceExpression program context source place type mutable ∧ capture ∈ captures ∧ capture.place = place ∧ capture.mode = .own) →
        Fresh context localSlot → localSlot.type = .callable function.declaration [] →
        Expression program context (.capture places source) localSlot.type (AtomCode localSlot (.closure function.declaration [] captures))
    | label {context name annotation body type brand region code} :
        (annotation = none ∨ ∃ source, annotation = some source ∧ TypeExpression program context source .type type) →
        Expression program { context with namedLabels := (name,brand) :: context.namedLabels, typed := { context.typed with labels := (brand,.rigid region .region 0,type) :: context.typed.labels } } body type code →
        Expression program context (.label name annotation body) type (.scope region (.label brand region type code))
    | test {context subject sourcePattern subjectLocal subjectCode type pattern names patternId result nextType} :
        Fresh context subjectLocal → subjectLocal.type = type → Expression program context subject type subjectCode →
        PatternExpression program context sourcePattern type .shared pattern names → Fresh context result → result.type = nextType →
        (∃ carrier arguments, program.declarations.input.manifest.testCarrier = some carrier ∧ nextType = .nominal carrier.declaration arguments) →
        Expression program context (.test subject sourcePattern) nextType
          (.evaluate subjectLocal subjectCode (.test result ⟨subjectLocal.id,[]⟩ pattern patternId (.result ⟨result.id,[]⟩)))
    | handle {context source arms computation input handler result identity} : Handler program context arms input handler →
        Expression program context source input computation → handler.result = result →
        Expression program context (.handle source arms) result (.handle identity computation handler)
    | unsafeAllowed {context source type body} : Expression program { context with typed := { context.typed with static := { context.typed.static with unsafeAllowed := true } } } source type body →
        Expression program context (.unsafeBlock source) type (.unsafeScope body)
    | operators {context first rest grouped type code} : Grouped program.declarations context.typed.static.module first rest grouped →
        Expression program context grouped type code → Expression program context (.operators first rest) type code
    | prefixForm {context operator operand fixity path header type code} : FixitySelected program.declarations context.typed.static.module operator true fixity →
        Qualified program.declarations context.typed.static.module .value path header → header.id = fixity.target →
        Expression program context (.call (.name path [] []) [operand]) type code → Expression program context (.prefixForm operator operand) type code
    | coercion {context source actual expected code} : Expression program context source actual code →
        Subtype program.declarations context.typed.static actual expected → Expression program context source expected code

  inductive Arguments (program : Kernel.Program) : Context → List Source.Expr → List Term → List BindingCode → List Place → Prop where
    | nil {context} : Arguments program context [] [] [] []
    | cons {context source sources type types localSlot code rest places} : Fresh context localSlot → localSlot.type = type →
        Expression program context source type code →
        Arguments program { context with typed := context.typed.bind localSlot } sources types rest places →
        Arguments program context (source :: sources) (type :: types) (⟨localSlot,code⟩ :: rest) (⟨localSlot.id,[]⟩ :: places)

  inductive Block (program : Kernel.Program) : Context → List Source.Statement → Option Source.Expr → Term → Code → Prop where
    | result {context source type code} : Expression program context source type code → Block program context [] (some source) type code
    | unit {context localSlot} : Fresh context localSlot → localSlot.type = .unit →
        Block program context [] none .unit (AtomCode localSlot (.constant (.constantTuple [])))
    | bind {context mutable sourcePattern annotation source rest result type localSlot initializer pattern names body resultType} :
        Fresh context localSlot → localSlot.type = type → Expression program context source type initializer →
        (annotation = none ∨ ∃ sourceType, annotation = some sourceType ∧ TypeExpression program context sourceType .type type) →
        PatternExpression program context sourcePattern type .owned pattern names → (∀ entry ∈ names, entry.2.mutable = mutable) →
        Block program (BindNames context names) rest result resultType body →
        Typing.PatternCoverage program type [.clause pattern body] →
        Block program context (.bind mutable sourcePattern annotation source :: rest) result resultType
          (.evaluate localSlot initializer (.choose ⟨localSlot.id,[]⟩ [.clause pattern body]))
    | assign {context destination source rest result type localSlot initializer place body resultType} :
        Fresh context localSlot → localSlot.type = type → Expression program context source type initializer →
        PlaceExpression program context destination place type true → Block program context rest result resultType body →
        Block program context (.assign destination source :: rest) result resultType
          (.evaluate localSlot initializer (.assign place ⟨localSlot.id,[]⟩ body))
    | discard {context source rest result localSlot initializer body resultType} : Fresh context localSlot →
        Expression program context source localSlot.type initializer → Block program context rest result resultType body →
        Block program context (.discard source :: rest) result resultType (.evaluate localSlot initializer (.discard ⟨localSlot.id,[]⟩ body))
    | item {context declaration rest result body type} : Declaration program context declaration →
        Block program context rest result type body → Block program context (.item declaration :: rest) result type body

  inductive Closure (program : Kernel.Program) : Context → Source.Expr → Signature → Function → List Capture → Prop where
    | function {context head body signature function captures sources inner parameterNames bodyCode declaration} :
        Head program context head signature → function.signature = signature → program.function function.declaration = some function →
        program.declarations.function function.declaration = some declaration → declaration.header.sourceVisible = false →
        declaration.origin = .source context.origin →
        CapturesResolved program context sources captures function.captures → ExtendsWithCaptures context inner sources function.captures →
        Parameters program inner head.parameters function.parameters parameterNames →
        Expression program (BindNames inner parameterNames) body signature.result bodyCode → function.body = bodyCode →
        Contracts.ResourceAdmission program function → Closure program context (.function head body) signature function captures
    | clauses {context arms signature function captures sources inner code declaration} : function.signature = signature →
        program.function function.declaration = some function → program.declarations.function function.declaration = some declaration →
        declaration.header.sourceVisible = false → CapturesResolved program context sources captures function.captures →
        declaration.origin = .source context.origin →
        ExtendsWithCaptures context inner sources function.captures →
        PatternCallable program inner arms signature function.parameters code → function.body = code →
        Contracts.ResourceAdmission program function → Closure program context (.clauses arms) signature function captures
    | block {context statements result signature function captures sources inner body declaration} : function.signature = signature →
        program.function function.declaration = some function → program.declarations.function function.declaration = some declaration →
        declaration.header.sourceVisible = false → CapturesResolved program context sources captures function.captures →
        declaration.origin = .source context.origin →
        ExtendsWithCaptures context inner sources function.captures →
        (∀ parameter ∈ function.parameters, ∃ principal, PrincipalOf program.declarations parameter.type principal ∧ principal.MayDiscard) →
        Block program inner statements result signature.result body → function.body = body →
        Contracts.ResourceAdmission program function → Closure program context (.block statements result) signature function captures

  inductive PatternCallable (program : Kernel.Program) : Context → List (Source.Pattern × Source.Expr) → Signature → List Local → Code → Prop where
    | single {context arms signature parameter kernelArms} : signature.parameters = [parameter.type] →
        PatternArms program context arms parameter.type signature.result kernelArms → Typing.PatternCoverage program parameter.type kernelArms →
        PatternCallable program context arms signature [parameter] (.choose ⟨parameter.id,[]⟩ kernelArms)
    | tuple {context arms signature parameters tuple kernelArms} : parameters.length ≠ 1 → parameters.map (·.type) = signature.parameters →
        Fresh context tuple → tuple.type = .tuple signature.parameters →
        PatternArms program context arms tuple.type signature.result kernelArms → Typing.PatternCoverage program tuple.type kernelArms →
        PatternCallable program context arms signature parameters
          (.bind tuple (.construct tuple.type none (parameters.map (fun localSlot => ⟨localSlot.id,[]⟩))) (.choose ⟨tuple.id,[]⟩ kernelArms))

  inductive PatternArms (program : Kernel.Program) : Context → List (Source.Pattern × Source.Expr) → Term → Term → List Arm → Prop where
    | nil {context input output} : PatternArms program context [] input output []
    | cons {context sourcePattern sourceBody rest input output pattern names body arms} :
        PatternExpression program context sourcePattern input .owned pattern names → Expression program (BindNames context names) sourceBody output body →
        PatternArms program context rest input output arms →
        PatternArms program context ((sourcePattern,sourceBody) :: rest) input output (.clause pattern body :: arms)

  inductive Handler (program : Kernel.Program) : Context → List Source.HandlerArm → Term → Kernel.Handler → Prop where
    | attached {context source input result completion operations captures} :
        HandlerArms program context source input result completion operations →
        Typing.HandlerType program context.typed (.attached result completion operations captures) input result →
        Handler program context source input (.attached result completion operations captures)

  inductive HandlerArms (program : Kernel.Program) :
      Context → List Source.HandlerArm → Term → Term → List Arm → List OperationArm → Prop where
    | nil {context input output} : HandlerArms program context [] input output [] []
    | completion {context sourcePattern sourceBody rest input output pattern names body completion operations} :
        PatternExpression program context sourcePattern input .owned pattern names → Expression program (BindNames context names) sourceBody output body →
        HandlerArms program context rest input output completion operations →
        HandlerArms program context (.completion sourcePattern sourceBody :: rest) input output (.clause pattern body :: completion) operations
    | operation {context path sourceArguments sourcePatterns sourceBody rest input output header operation arguments signature
        patterns names continuation body completion operations bodyResult} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.operation header.id = some operation →
        TypeExpressions program context sourceArguments (operation.signature.generics.map (·.kind)) arguments →
        Typing.CallSignature program.declarations context.typed.static header.id arguments signature →
        PatternExpressions program context sourcePatterns (signature.parameters ++ continuation.toList.map Local.type) .owned
          patterns names →
        Expression program (BindNames context names) sourceBody bodyResult body →
        Typing.OperationArmsType program context.typed [.clause header.id arguments [] (patterns.take signature.parameters.length) continuation body] output →
        HandlerArms program context rest input output completion operations →
        HandlerArms program context (.operation path sourceArguments sourcePatterns sourceBody :: rest) input output completion
          (.clause header.id arguments [] (patterns.take signature.parameters.length) continuation body :: operations)

  inductive Head (program : Kernel.Program) : Context → Source.FunctionHead → Signature → Prop where
    | head {context source binders extended parameters result effects requirements} :
        Generics program context source.generics binders extended →
        TypeExpressions program extended (source.parameters.map (·.type)) (List.replicate source.parameters.length .type) parameters →
        TypeExpression program extended source.result .type result →
        (TypeExpression program extended source.effects .row effects ∨
          ∃ instanceTerm, TypeExpression program extended source.effects .effect instanceTerm ∧ effects = .row [instanceTerm] []) →
        Predicates program extended source.requirements requirements →
        Head program context source ⟨binders,parameters,result,effects,requirements,source.unsafeAllowed⟩

  inductive Parameters (program : Kernel.Program) : Context → List Source.Parameter → List Local → List (String × Local) → Prop where
    | nil {context} : Parameters program context [] [] []
    | cons {context source rest localSlot type pattern names locals more} : TypeExpression program context source.type .type type → localSlot.type = type →
        PatternExpression program context source.pattern type .owned pattern names →
        Parameters program (BindNames context names) rest locals more →
        Parameters program context (source :: rest) (localSlot :: locals) (names ++ more)

  inductive Generics (program : Kernel.Program) : Context → List Source.Generic → List Binder → Context → Prop where
    | nil {context} : Generics program context [] [] context
    | cons {context source rest binder middle binders final} : binder.name = source.name → binder.kind = source.kind →
        (∀ old ∈ context.typed.static.binders, old.id ≠ binder.id ∧ old.name ≠ binder.name) →
        ((source.defaultValue = none ∧ binder.defaultValue = none) ∨ ∃ sourceDefault value,
          source.defaultValue = some sourceDefault ∧ binder.defaultValue = some value ∧ TypeExpression program context sourceDefault binder.kind value) →
        middle = { context with typed := { context.typed with static := { context.typed.static with binders := context.typed.static.binders ++ [binder] } } } →
        Generics program middle rest binders final → Generics program context (source :: rest) (binder :: binders) final

  inductive Predicate (program : Kernel.Program) : Context → Source.Predicate → List Constraint → Prop where
    | callable {context source traitPath sourceArguments receiver header trait argumentTypes arguments output effects safe} :
        TypeExpression program context source .type receiver → Qualified program.declarations context.typed.static.module .trait traitPath header →
        program.declarations.trait header.id = some trait → trait.relation = .callable →
        TypeExpression program context argumentTypes .type (.tuple arguments) →
        FnArguments program context sourceArguments argumentTypes output effects →
        Predicate program context (.bound source traitPath sourceArguments safe false) [.callable receiver arguments output effects safe]
    | runsIn {context source traitPath sourceArguments receiver header trait accessType tupleType afterType access arguments after safe} :
        TypeExpression program context source .type receiver → Qualified program.declarations context.typed.static.module .trait traitPath header →
        program.declarations.trait header.id = some trait → trait.relation = .runsIn →
        sourceArguments = [accessType,tupleType,.binding "After" afterType] →
        TypeExpression program context accessType .type access → TypeExpression program context tupleType .type (.tuple arguments) →
        TypeExpression program context afterType .type after →
        Predicate program context (.bound source traitPath sourceArguments safe false) [.runsIn receiver access arguments after safe]
    | equal {context a b left right kind} : TypeExpression program context a kind left → TypeExpression program context b kind right →
        Predicate program context (.equal a b) [.equal left right]
    | outlives {context a b left right} : TypeExpression program context a .region left → TypeExpression program context b .region right →
        Predicate program context (.outlives a b) [.outlives left right]
    | typeOutlives {context a b left right} : TypeExpression program context a .type left → TypeExpression program context b .region right →
        Predicate program context (.outlives a b) [.typeOutlives left right]
    | bound {context source traitPath sourceArguments safe negative receiver header trait arguments} :
        TypeExpression program context source .type receiver → Qualified program.declarations context.typed.static.module .trait traitPath header →
        program.declarations.trait header.id = some trait → trait.relation = .ordinary →
        TypeExpressions program context sourceArguments (trait.generics.drop 1 |>.map (·.kind)) arguments →
        (safe = true → trait.unsafeAllowed = true) →
        Predicate program context (.bound source traitPath sourceArguments safe negative) [.implements header.id (receiver :: arguments) negative]
    | use {context source traitPath quantity receiver header trait} : TypeExpression program context source .type receiver →
        Qualified program.declarations context.typed.static.module .trait traitPath header → program.declarations.trait header.id = some trait →
        trait.relation = .use → Predicate program context (.bound source traitPath [.quantity quantity] false false) [.use receiver quantity]
    | quantified {context sourceBinders sourceRequirements binders inner constraints} :
        Generics program context (sourceBinders.map (fun (name,kind) => ⟨name,kind,none,none⟩)) binders inner →
        Predicates program inner sourceRequirements constraints →
        Predicate program context (.quantified sourceBinders sourceRequirements) [.quantified binders constraints]

  inductive Predicates (program : Kernel.Program) : Context → List Source.Predicate → List Constraint → Prop where
    | nil {context} : Predicates program context [] []
    | cons {context source rest constraints more} : Predicate program context source constraints → Predicates program context rest more →
        Predicates program context (source :: rest) (constraints ++ more)

  inductive Declaration (program : Kernel.Program) : Context → Source.Declaration → Prop where
    | visible {context visibility source} : Declaration program { context with visibility := visibility } source →
        Declaration program context (.visible visibility source)
    | attributed {context attributes source} : Declaration program { context with attributes := context.attributes ++ attributes } source →
        Declaration program context (.attributed attributes source)
    | foreign {context members unsafeAllowed} : Declarations program context members →
        (∀ member ∈ members, ∃ head, member = .function head none ∧ head.generics = [] ∧ (unsafeAllowed = true → head.unsafeAllowed = true)) →
        Declaration program context (.foreign members unsafeAllowed)
    | inherent {context generics self requirements members unsafeAllowed binders inner type constraints id arguments} :
        Generics program context generics binders inner → TypeExpression program inner self .type type →
        type = .nominal id arguments → Predicates program inner requirements constraints →
        Declarations program { inner with selfType := some type, owner := some id, typed := { inner.typed with static := { inner.typed.static with assumptions := constraints ++ inner.typed.static.assumptions } } } members →
        Declaration program context (.implementation generics none self requirements members unsafeAllowed false)
    | checked {context source definition} : DeclarationHeader program context source definition →
        (definition.header.id,context.origin) ∈ program.declarations.origins →
        definition.header.visibility = context.visibility → AttributeContract context.attributes definition →
        DeclarationBody program context source definition → Declaration program context source

  inductive DeclarationHeader (program : Kernel.Program) : Context → Source.Declaration → Definition → Prop where
    | function {context head body definition signature} : Definition.function definition ∈ program.declarations.declarations →
        definition.header.name = head.name → definition.header.module = context.typed.static.module →
        Head program context head signature → signature = definition.signature → definition.cABI = head.cABI →
        definition.owner = context.owner →
        DeclarationHeader program context (.function head body) (.function definition)
    | data {context name sourceGenerics fields record requirements definition binders inner constraints} :
        Definition.data definition ∈ program.declarations.declarations → definition.header.name = name → definition.isEnum = false →
        Generics program context sourceGenerics binders inner → definition.generics = binders →
        Predicates program inner requirements constraints → definition.requirements = constraints →
        DeclarationHeader program context (.structure name sourceGenerics fields record requirements) (.data definition)
    | enumeration {context name sourceGenerics variants requirements definition binders inner constraints} :
        Definition.data definition ∈ program.declarations.declarations → definition.header.name = name → definition.isEnum = true →
        Generics program context sourceGenerics binders inner → definition.generics = binders →
        Predicates program inner requirements constraints → definition.requirements = constraints →
        DeclarationHeader program context (.enumeration name sourceGenerics variants requirements) (.data definition)
    | alias {context name sourceGenerics value definition binders inner type} : Definition.alias definition ∈ program.declarations.declarations →
        definition.header.name = name → Generics program context sourceGenerics binders inner → definition.generics = binders →
        TypeExpression program inner value .type type → definition.value = type →
        DeclarationHeader program context (.alias name sourceGenerics value) (.alias definition)
    | item {context source definition} : ItemHeader program context source definition → DeclarationHeader program context source definition

  inductive DeclarationBody (program : Kernel.Program) : Context → Source.Declaration → Definition → Prop where
    | function {context head source definition function names inner code} :
        program.function definition.header.id = some function → definition.origin = .source context.origin →
        Parameters program context head.parameters function.parameters names →
        inner = { (BindNames context names) with namedLabels := (head.name,function.namedExit.getD 0) :: context.namedLabels, typed := { (BindNames context names).typed with effects := function.signature.effects, labels := (function.namedExit.getD 0,.rigid (function.namedExit.getD 0) .region 0,function.signature.result) :: context.typed.labels } } →
        Expression program (inner.child 0) source function.signature.result code → function.body = code → function.signature = definition.signature →
        DeclarationBody program context (.function head (some source)) (.function definition)
    | bodyless {context head definition} :
        ((∃ trait, definition.origin = .traitMember trait ∧ context.owner = some trait) ∨ definition.origin = .foreign ∨
          (definition.origin = .runtime program.declarations.input.manifest.identity ∧
            ∃ binding ∈ program.declarations.input.manifest.bindings, binding.declaration = definition.header.id ∧ binding.signature = definition.signature)) →
        DeclarationBody program context (.function head none) (.function definition)
    | data {context name sourceGenerics fields record requirements definition variant inner binders} :
        Generics program context sourceGenerics binders inner → definition.variants = [variant] →
        SourceFields program inner fields variant.fields →
        DeclarationBody program context (.structure name sourceGenerics fields record requirements) (.data definition)
    | enumeration {context name sourceGenerics variants requirements definition inner binders} :
        Generics program context sourceGenerics binders inner → SourceVariants program inner variants definition.variants →
        DeclarationBody program context (.enumeration name sourceGenerics variants requirements) (.data definition)
    | alias {context name generics value definition} : DeclarationBody program context (.alias name generics value) (.alias definition)
    | item {context source definition} : ItemBody program context source definition → DeclarationBody program context source definition

  inductive SourceFields (program : Kernel.Program) : Context → List Source.Field → List FieldDefinition → Prop where
    | nil {context} : SourceFields program context [] []
    | cons {context source rest field fields type} : TypeExpression program context source.type .type type → field.type = type →
        field.header.visibility = source.visibility → field.header.name = source.name.getD (toString fields.length) →
        SourceFields program context rest fields → SourceFields program context (source :: rest) (field :: fields)

  inductive SourceVariants (program : Kernel.Program) : Context → List Source.Variant → List VariantDefinition → Prop where
    | nil {context} : SourceVariants program context [] []
    | cons {context source rest variant variants} : source.name = variant.header.name → SourceFields program context source.fields variant.fields →
        SourceVariants program context rest variants → SourceVariants program context (source :: rest) (variant :: variants)

  inductive ItemHeader (program : Kernel.Program) : Context → Source.Declaration → Definition → Prop where
    | named {context source definition name nameSpace} : definition ∈ program.declarations.declarations →
        SourceItemName source name nameSpace → definition.header.name = name → definition.header.nameSpace = nameSpace →
        definition.header.module = context.typed.static.module → ItemHeader program context source definition

  inductive ItemBody (program : Kernel.Program) : Context → Source.Declaration → Definition → Prop where
    | trait {context name generics requirements members unsafeAllowed definition binders inner constraints} :
        Generics program context generics binders inner → Predicates program inner requirements constraints →
        definition.generics = binders → definition.requirements = constraints → definition.unsafeAllowed = unsafeAllowed →
        MemberIdentities program inner members definition.members →
        Declarations program { inner with owner := some definition.header.id } members →
        ItemBody program context (.trait name generics requirements members unsafeAllowed) (.trait definition)
    | effect {context name generics requirements operations definition binders inner constraints} :
        Generics program context generics binders inner → Predicates program inner requirements constraints →
        definition.generics = binders → definition.requirements = constraints →
        SourceOperations program inner definition.header.id operations definition.operations →
        ItemBody program context (.effect name generics requirements operations) (.effect definition)
    | constant {context name generics sourceType sourceValue definition binders inner type value} :
        Generics program context generics binders inner → definition.generics = binders → TypeExpression program inner sourceType .type type →
        StructuralConstant program inner sourceValue type value → definition.type = type → definition.value = value →
        ItemBody program context (.constant name generics sourceType sourceValue) (.constant definition)
    | global {context name sourceType sourceValue definition type code} :
        (∃ annotation, sourceType = some annotation ∧ TypeExpression program context annotation .type type) → definition.type = type →
        Expression program context sourceValue type code → definition.initializer = context.origin →
        ItemBody program context (.global name sourceType sourceValue) (.global definition)
    | import {context tree definition} : definition.tree = tree → definition.prelude = false →
        ItemBody program context (.import tree) (.import definition)
    | module {context name members definition} : definition.header.name = name →
        ((members = none ∧ definition.inline = false) ∨ ∃ declarations, members = some declarations ∧ definition.inline = true ∧
          Declarations program { context with typed := { context.typed with static := { context.typed.static with module := definition.module } } } declarations) →
        ItemBody program context (.module name members) (.module definition)
    | fixity {context kind precedence operator target definition header} : definition.kind = kind → definition.precedence = precedence →
        definition.operator = operator → Qualified program.declarations context.typed.static.module .value (target.getD [operator]) header →
        definition.target = header.id → ItemBody program context (.fixity kind precedence operator target) (.fixity definition)
    | associated {context name generics kind requirements sourceValue definition binders inner constraints} :
        Generics program context generics binders inner → definition.generics = binders → definition.kind = kind →
        Predicates program inner requirements constraints → definition.requirements = constraints → context.owner = some definition.owner →
        ((sourceValue = none ∧ definition.defaultValue = none) ∨ ∃ source value, sourceValue = some source ∧ definition.defaultValue = some value ∧
          TypeExpression program inner source kind value) →
        ItemBody program context (.associated name generics kind requirements sourceValue) (.associated definition)
    | implementation {context generics traitPath traitArguments self requirements members unsafeAllowed negative definition
        binders inner type header trait arguments constraints} :
        Generics program context generics binders inner → TypeExpression program inner self .type type →
        Qualified program.declarations context.typed.static.module .trait traitPath header →
        program.declarations.trait header.id = some trait → TypeExpressions program inner traitArguments (trait.generics.drop 1 |>.map (·.kind)) arguments →
        Predicates program inner requirements constraints → definition.generics = binders → definition.trait = header.id →
        definition.arguments = type :: arguments → definition.requirements = constraints → definition.unsafeAllowed = unsafeAllowed → definition.negative = negative →
        (negative = true → members = [] ∧ definition.associated = [] ∧ definition.functions = []) →
        Declarations program { inner with owner := some header.id, selfType := some type, typed := { inner.typed with static := { inner.typed.static with assumptions := constraints ++ inner.typed.static.assumptions } } } members →
        ItemBody program context (.implementation generics (some (.path traitPath traitArguments [])) self requirements members unsafeAllowed negative)
          (.implementation definition)

  inductive Declarations (program : Kernel.Program) : Context → List Source.Declaration → Prop where
    | nil {context} : Declarations program context []
    | cons {context source rest} : Declaration program (context.child context.itemIndex) source →
        Declarations program { context with itemIndex := context.itemIndex+1 } rest →
        Declarations program context (source :: rest)

  inductive SourceOperations (program : Kernel.Program) : Context → DeclId → List Source.Operation → List DeclId → Prop where
    | nil {context family} : SourceOperations program context family [] []
    | cons {context family source rest id ids definition binders inner parameters result constraints} :
        program.declarations.operation id = some definition → definition.header.name = source.name → definition.family = family →
        Generics program context source.generics binders inner →
        TypeExpressions program inner source.payload (List.replicate source.payload.length .type) parameters →
        TypeExpression program inner source.result .type result → Predicates program inner source.requirements constraints →
        definition.signature = ⟨context.typed.static.binders ++ binders,parameters,result,
          .row [.effect family (context.typed.static.binders.map (fun binder => .parameter binder.id binder.kind))] [],constraints,false⟩ →
        ((result = .bottom ∧ source.quantity = none ∧ definition.terminal = true ∧ definition.quantity = none) ∨
          (result ≠ .bottom ∧ definition.terminal = false ∧ definition.quantity = some (source.quantity.getD ⟨1,some 1⟩))) →
        SourceOperations program context family rest ids → SourceOperations program context family (source :: rest) (id :: ids)

  inductive StructuralConstant (program : Kernel.Program) : Context → Source.Expr → Term → Term → Prop where
    | literal {context source type value} : LiteralConstant program.declarations.input.target source (some type) value type →
        StructuralConstant program context (.literal source) type value
    | unit {context} : StructuralConstant program context .unit .unit (.constantTuple [])
    | alias {context path sourceArguments type value} : ConstantAlias program context path sourceArguments value type →
        StructuralConstant program context (.name path sourceArguments []) type value
    | tuple {context sources types values} : ListRel (fun source pair => StructuralConstant program context source pair.1 pair.2) sources (types.zip values) →
        types.length = values.length → StructuralConstant program context (.tuple sources) (.tuple types) (.constantTuple values)
    | constructor {context path sourceArguments sources header data variant arguments substitution types values} :
        Qualified program.declarations context.typed.static.module .value path header → program.declarations.Constructor header.id data variant →
        TypeExpressions program context sourceArguments (data.generics.map (·.kind)) arguments → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        ListRel (fun source pair => StructuralConstant program context source pair.1 pair.2) sources (types.zip values) → types.length = values.length →
        StructuralConstant program context (.call (.name path sourceArguments []) sources) (.nominal data.header.id arguments)
          (.constantConstructor header.id arguments values)

  inductive FnArguments (program : Kernel.Program) : Context → List Source.TypeExpr → Source.TypeExpr → Term → Term → Prop where
    | explicit {context argumentTuple sourceOutput sourceEffects output effects} : TypeExpression program context sourceOutput .type output →
        TypeExpression program context sourceEffects .row effects →
        FnArguments program context [argumentTuple,.binding "Output" sourceOutput,.binding "effects" sourceEffects] argumentTuple output effects
    | result {context argumentTuple sourceOutput output} : TypeExpression program context sourceOutput .type output →
        FnArguments program context [argumentTuple,.binding "Output" sourceOutput] argumentTuple output (.row [] [])
    | inferred {context argumentTuple output effects} : Kinding program.declarations context.typed.static output .type →
        Kinding program.declarations context.typed.static effects .row → FnArguments program context [argumentTuple] argumentTuple output effects
end

end Glorious.Language.Elaboration
