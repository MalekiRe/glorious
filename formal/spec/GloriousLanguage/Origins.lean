import GloriousLanguage.Elaboration

/-! Source closure and origin authentication. Every semantic declaration has
an origin in the supplied files or an explicitly admitted manifest binding;
there is no implicit filesystem or ambient declaration search. -/
namespace Glorious.Language.Source

inductive Node where
  | declaration (value : Declaration)
  | expression (value : Expr)
  | statement (value : Statement)
  | handlerArm (value : HandlerArm)
  | operation (value : Operation)
  deriving Repr, Inhabited

mutual
  def declarationChildren : Declaration → List Node
    | .function _ body => body.toList.map .expression
    | .trait _ _ _ members _ | .implementation _ _ _ _ members _ _ => members.map .declaration
    | .effect _ _ _ operations => operations.map .operation
    | .constant _ _ _ value | .global _ _ value => [.expression value]
    | .module _ members => members.toList.flatten.map .declaration
    | .foreign members _ => members.map .declaration
    | .visible _ declaration | .attributed _ declaration => declarationChildren declaration
    | _ => []

  def expressionChildren : Expr → List Node
    | .tuple fields | .array fields => fields.map .expression
    | .call callee arguments | .tail callee arguments => .expression callee :: arguments.map .expression
    | .block statements result => statements.map .statement ++ result.toList.map .expression
    | .function _ body => [.expression body]
    | .clauses arms => arms.map (fun arm => .expression arm.2)
    | .capture places body => places.map .expression ++ [.expression body]
    | .project source _ | .borrow _ source | .dereference source | .move source | .test source _ => [.expression source]
    | .handle computation arms => .expression computation :: arms.map .handlerArm
    | .label _ _ body | .unsafeBlock body | .prefixForm _ body => [.expression body]
    | .operators first rest => .expression first :: rest.map (fun pair => .expression pair.2)
    | _ => []

  def statementChildren : Statement → List Node
    | .bind _ _ _ value | .discard value => [.expression value]
    | .assign destination value => [.expression value,.expression destination]
    | .item declaration => [.declaration declaration]
end

def Node.children : Node → List Node
  | .declaration item => declarationChildren item
  | .expression source => expressionChildren source
  | .statement source => statementChildren source
  | .handlerArm (.completion _ body) | .handlerArm (.operation _ _ _ body) => [.expression body]
  | .operation _ => []

inductive Descends : Node → List Nat → Node → Prop where
  | here {node} : Descends node [] node
  | child {node index child path selected} : node.children[index]? = some child → Descends child path selected →
      Descends node (index :: path) selected

def NodeAt (declarations : List Declaration) (path : List Nat) (node : Node) : Prop :=
  ∃ index rest declaration, path = index :: rest ∧ declarations[index]? = some declaration ∧ Descends (.declaration declaration) rest node

def Declaration.undecorated : Declaration → Declaration
  | .visible _ declaration | .attributed _ declaration => declaration.undecorated
  | declaration => declaration

def SourceEntity (node : Node) (definition : Definition) : Prop :=
  match node, definition with
  | .declaration source, .function function =>
      ∃ head body, source.undecorated = .function head body ∧ function.header.name = head.name
  | .expression source, .function function =>
      function.header.sourceVisible = false ∧
      ((∃ head body, source = .function head body) ∨ (∃ arms, source = .clauses arms) ∨
        (∃ statements result, source = .block statements result) ∨ ∃ places body, source = .capture places body)
  | .declaration source, .data data =>
      (∃ name generics fields record requirements, source.undecorated = .structure name generics fields record requirements ∧ data.header.name = name) ∨
      ∃ name generics variants requirements, source.undecorated = .enumeration name generics variants requirements ∧ data.header.name = name
  | .declaration source, .alias alias => ∃ generics value, source.undecorated = .alias alias.header.name generics value
  | .declaration source, .trait trait => ∃ generics requirements members unsafeAllowed,
      source.undecorated = .trait trait.header.name generics requirements members unsafeAllowed
  | .declaration source, .associated associated => ∃ generics kind requirements value,
      source.undecorated = .associated associated.header.name generics kind requirements value
  | .declaration source, .implementation _ => ∃ generics trait self requirements members unsafeAllowed negative,
      source.undecorated = .implementation generics trait self requirements members unsafeAllowed negative
  | .declaration source, .effect effect => ∃ generics requirements operations,
      source.undecorated = .effect effect.header.name generics requirements operations
  | .operation source, .operation operation => source.name = operation.header.name
  | .declaration source, .constant constant => ∃ generics type value,
      source.undecorated = .constant constant.header.name generics type value
  | .declaration source, .global global => ∃ type value, source.undecorated = .global global.header.name type value
  | .declaration source, .module module => ∃ members, source.undecorated = .module module.header.name members
  | .declaration source, .import imported => source.undecorated = .import imported.tree
  | .declaration source, .fixity fixity => ∃ target, source.undecorated = .fixity fixity.kind fixity.precedence fixity.operator target
  | .expression _, .environment environment => environment.header.sourceVisible = false
  | _, _ => False

end Glorious.Language.Source

namespace Glorious.Language.Elaboration

structure ParsedFile where
  file : Source.File
  declarations : List Source.Declaration
  deriving Repr, Inhabited

def ParsedClosure (program : Kernel.Program) (files : List ParsedFile) : Prop :=
  files.map (·.file) = program.declarations.input.files ∧
  ∀ file ∈ files, Source.ParsedAs file.file file.declarations

def AuthenticatedOrigins (program : Kernel.Program) (files : List ParsedFile) : Prop :=
  (program.declarations.origins.map Prod.fst).Nodup ∧
  (∀ id anchor, (id,anchor) ∈ program.declarations.origins → ∃ definition file node,
    program.declarations.lookup id = some definition ∧ file ∈ files ∧ file.file.id = anchor.file ∧
    Source.NodeAt file.declarations anchor.node node ∧ Source.SourceEntity node definition ∧
    definition.header.id.package = file.file.package ∧ definition.header.span.file = file.file.id ∧
    definition.header.span.start ≤ definition.header.span.stop ∧ definition.header.span.stop ≤ file.file.bytes.length) ∧
  (∀ definition ∈ program.declarations.declarations,
    (∃ anchor, (definition.header.id,anchor) ∈ program.declarations.origins) ∨
      (∃ module, definition = .module module ∧ module.parent = none ∧
        ∃ package ∈ program.declarations.input.packages, package.id = module.module.package ∧ package.root = module.file) ∨
      (∃ binding ∈ program.declarations.input.manifest.bindings, binding.declaration = definition.header.id) ∨
      (∃ relation, (definition.header.id,relation) ∈ program.declarations.input.manifest.sealedRelations))

def FileElaborates (program : Kernel.Program) (file : ParsedFile) : Prop :=
  ∃ module, Definition.module module ∈ program.declarations.declarations ∧ module.file = file.file.id ∧ module.inline = false ∧
    Declarations program
      { typed := ⟨⟨[],[],0,module.module,false⟩,[],[],.row [] [],none⟩,
        origin := ⟨file.file.id,[]⟩ }
      file.declarations

def SourceProgram (program : Kernel.Program) : Prop :=
  ∃ files, ParsedClosure program files ∧ AuthenticatedOrigins program files ∧ ∀ file ∈ files, FileElaborates program file

end Glorious.Language.Elaboration
