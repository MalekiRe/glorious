import Glorious.Semantics.Lexer

namespace Glorious.Semantics

structure ParserState where
  tokens : Array Token
  position : Nat := 0
  nextId : Nat := 1
  module : ModuleId
  program : Program
  binders : List Binder := []
  selfType : Option Term := none
  currentOwner : Option Term := none
  implicitRegions : List Binder := []
  inputRegions : List Term := []
  parsingResult : Bool := false
  deriving Repr

abbrev ParseM := StateT ParserState Check

def peek : ParseM Token := do
  let state ← get
  return state.tokens[state.position]?.getD ⟨.eof, {}⟩

def peekAt (offset : Nat) : ParseM Token := do
  let state ← get
  return state.tokens[state.position + offset]?.getD ⟨.eof, {}⟩

def takeToken : ParseM Token := do
  let token ← peek
  modify fun state => { state with position := state.position + 1 }
  return token

def accept (spelling : String) : ParseM Bool := do
  if (← peek).spelling == spelling then let _ ← takeToken; return true else return false

def expect (spelling : String) : ParseM Token := do
  let token ← takeToken
  require (token.spelling == spelling) .invalidSource s!"expected {spelling}, found {token.spelling}" token.span
  return token

def identifier : ParseM (String × Span) := do
  let token ← takeToken
  match token.kind with
  | .identifier name => return (name, token.span)
  | _ => reject .invalidSource "expected an identifier" token.span

def parserId : ParseM Id := do
  let state ← get
  set { state with nextId := state.nextId + 1 }
  return state.nextId

def parserDecl (name : String) (span : Span) (visibility : Visibility) : ParseM DeclHeader := do
  let state ← get
  let id ← parserId
  return ⟨⟨state.module.packageId, id⟩, state.module, name, visibility, span⟩

def parsePath (fuel : Nat) : ParseM Path := do
  let (first, _) ← identifier
  let rec rest : Nat → List String → ParseM Path
    | 0, _ => reject .resourceLimit "path parsing exhausted"
    | fuel + 1, names => do
      if (← peek).spelling == "::" && (← peekAt 1).spelling != "<" then
        let _ ← takeToken
        let (name, _) ← identifier
        rest fuel (names ++ [name])
      else return ⟨names⟩
  rest fuel [first]

def parseVisibility : ParseM Visibility := do
  if !(← accept "pub") then return .private
  if !(← accept "(") then return .public
  let token ← takeToken
  let _ ← expect ")"
  if token.spelling == "crate" then return .package
  if token.spelling == "super" then return .parent
  reject .invalidSource "unsupported restricted visibility" token.span

def parseSeparated (fuel : Nat) (closing : String) (parse : ParseM α) : ParseM (List α) := do
  let rec loop : Nat → List α → ParseM (List α)
    | 0, _ => reject .resourceLimit "delimited sequence parsing exhausted"
    | fuel + 1, values => do
      if ← accept closing then return values
      let value ← parse
      if ← accept "," then loop fuel (values ++ [value]) else
        let _ ← expect closing
        return values ++ [value]
  loop fuel []

mutual
  def parseTerm (fuel : Nat) (kind : Kind := .type) : ParseM Term := do
    match fuel with
    | 0 => reject .resourceLimit "type/constant parser exhausted"
    | fuel + 1 =>
      let token ← peek
      if ← accept "(" then
        let first ← if (← peek).spelling == ")" then pure none else pure (some (← parseTerm fuel kind))
        match first with
        | none => let _ ← expect ")"; return (if kind == .constant then .constantTuple [] else .unit)
        | some first =>
          if ← accept "," then
            let rest ← parseSeparated fuel ")" (parseTerm fuel kind)
            return if kind == .constant then .constantTuple (first :: rest) else .tuple (first :: rest)
          else let _ ← expect ")"; return first
      else if ← accept "!" then return .bottom
      else if ← accept "[" then
        if kind == .constant then
          let lower ← parseTerm fuel .constant
          let _ ← expect ","
          let upper ← if ← accept "*" then pure (.rigid 0 .constant 0) else parseTerm fuel .constant
          let _ ← expect "]"
          return .constantTuple [lower, upper]
        else
          let element ← parseTerm fuel .type
          let _ ← expect ";"
          let length ← parseTerm fuel .constant
          let _ ← expect "]"
          return .array element length
      else if ← accept "&" then
        let region ← match (← peek).kind with
          | .lifetime _ => parseTerm fuel .region
          | _ => do
            let state ← get
            if state.parsingResult && state.inputRegions.length == 1 then pure (state.inputRegions.headD .staticRegion) else
              let id ← parserId
              let binder : Binder := ⟨id, s!"_elided{id}", .region, none⟩
              let region := Term.param id .region
              modify fun state => { state with
                implicitRegions := state.implicitRegions ++ [binder],
                inputRegions := if state.parsingResult then state.inputRegions else state.inputRegions ++ [region] }
              pure region
        let mode := if ← accept "mut" then Mutability.unique else .shared
        return .reference mode region (← parseTerm fuel .type)
      else if ← accept "*" then
        let mode ← if ← accept "mut" then pure Mutability.unique else do let _ ← expect "const"; pure .shared
        return .rawPointer mode (← parseTerm fuel .type)
      else if (← peek).spelling == "{" then parseRow fuel
      else
        match token.kind with
        | .lifetime name =>
          let _ ← takeToken
          if name == "static" then return .staticRegion
          if name == "_" then
            let id ← parserId
            let binder : Binder := ⟨id, s!"_elided{id}", .region, none⟩
            modify fun state => { state with implicitRegions := state.implicitRegions ++ [binder] }
            return .param id .region
          let binder ← getRequired ((← get).binders.find? (fun b => b.name == name && b.kind == .region)) .unknownName "unknown lifetime parameter" token.span
          return .param binder.id .region
        | .number spelling =>
          let _ ← takeToken
          match ← numericLiteral spelling token.span with
          | .integer magnitude suffix negative =>
            let scalar := suffix.getD (.integer true .w64)
            let .integer signed width := scalar | reject .typeMismatch "integer const requires an integer suffix"
            return .constant (.integer signed width (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude))
          | _ => reject .invalidSource "floating literals are not structural const arguments" token.span
        | .character scalar byte =>
          let _ ← takeToken
          return .constant (if byte then .integer false .w8 (Int.ofNat scalar) else .character scalar)
        | .identifier _ =>
          let path ← parsePath fuel
          if path.components == ["Self"] then
            return ← getRequired (← get).selfType .unknownName "Self is outside an implementation"
          if let [name] := path.components then
            if let some binder := (← get).binders.find? (fun b => b.name == name) then return .param binder.id binder.kind
            if let some scalar := parseScalarType name then return .scalar scalar
          let arguments ← parseGenericArguments fuel
          return .named path.components arguments kind
        | _ => reject .invalidSource "expected a type, region, row or structural constant" token.span

  def parseGenericArguments (fuel : Nat) : ParseM (List Term) := do
    if !(← accept "<") then return []
    parseSeparated fuel ">" (do
      let token ← peek
      let kind := match token.kind with
        | .lifetime _ => Kind.region
        | .number _ | .character .. => Kind.constant
        | _ => if token.spelling == "[" then .constant else if token.spelling == "{" then .row else .type
      parseTerm fuel kind)

  def parseRow (fuel : Nat) : ParseM Term := do
    if !(← accept "{") then return .row [← parseTerm fuel .effect] []
    let rec known : Nat → List Term → ParseM Term
      | 0, _ => reject .resourceLimit "effect-row parser exhausted"
      | fuel + 1, instances => do
        if ← accept "}" then return .row instances []
        if ← accept "|" then
          let tails ← parseSeparated fuel "}" (parseTerm fuel .row)
          return .row instances tails
        let effectInstance ← parseTerm fuel .effect
        if ← accept "," then known fuel (instances ++ [effectInstance]) else
          if (← peek).spelling == "|" then known fuel (instances ++ [effectInstance]) else
            let _ ← expect "}"
            return .row (instances ++ [effectInstance]) []
    known fuel []

  def parseBinders (fuel : Nat) : ParseM (List Binder) := do
    if !(← accept "<") then return []
    let binders ← parseSeparated fuel ">" (do
      let constant := ← accept "const"
      let token ← takeToken
      let (name, kind) ← match token.kind with
        | .lifetime name => pure (name, Kind.region)
        | .identifier name => pure (name, if constant then Kind.constant else Kind.type)
        | _ => reject .invalidSource "invalid generic binder" token.span
      let kind ← if ← accept ":" then
          if (← peek).spelling == "EffectRow" then let _ ← takeToken; pure Kind.row
          else if constant then let _ ← parseTerm fuel .type; pure Kind.constant
          else
            let _ ← parsePath fuel
            let _ ← parseGenericArguments fuel
            pure kind
        else pure kind
      let id ← parserId
      let defaultValue ← if ← accept "=" then pure (some (← parseTerm fuel kind)) else pure none
      let binder : Binder := ⟨id, name, kind, defaultValue⟩
      modify fun state => { state with binders := state.binders ++ [binder] }
      pure binder)
    return binders

  def parseConstraints (fuel : Nat) : ParseM (List Constraint) := do
    if !(← accept "where") then return []
    let rec loop : Nat → List Constraint → ParseM (List Constraint)
      | 0, _ => reject .resourceLimit "where-clause parser exhausted"
      | fuel + 1, constraints => do
        if ["{", ";", "="].contains (← peek).spelling then return constraints
        let universal ← if ← accept "for" then parseBinders fuel else pure []
        let subject ← parseTerm fuel .type
        let newConstraints ← if ← accept "=" then pure [Constraint.equal subject (← parseTerm fuel subject.kind)] else do
          let _ ← expect ":"
          let rec bounds : Nat → List Constraint → ParseM (List Constraint)
            | 0, _ => reject .resourceLimit "bound list parser exhausted"
            | fuel + 1, result => do
              let bound ← match (← peek).kind with
                | .lifetime _ => pure (Constraint.outlives subject (← parseTerm fuel .region))
                | _ => do
                  let negative := ← accept "!"
                  let path ← parsePath fuel
                  let arguments ← parseGenericArguments fuel
                  pure (Constraint.named path.components (subject :: arguments) negative)
              if ← accept "+" then bounds fuel (result ++ [bound]) else return result ++ [bound]
          bounds fuel []
        let newConstraints := if universal.isEmpty then newConstraints else [.higherRanked universal newConstraints]
        if ← accept "," then loop fuel (constraints ++ newConstraints) else return constraints ++ newConstraints
    loop fuel []

  def parsePattern (fuel : Nat) : ParseM Pattern := do
    match fuel with
    | 0 => reject .resourceLimit "pattern parser exhausted"
    | fuel + 1 =>
      if ← accept "_" then return .wildcard
      if ← accept "let" then let (name, _) ← identifier; return .binder (← parserId) name true
      if ← accept "&" then
        let mode := if ← accept "mut" then Mutability.unique else .shared
        return .reference mode (← parsePattern fuel)
      if ← accept "(" then
        if ← accept ")" then return .tuple []
        let first ← parsePattern fuel
        if ← accept "," then return .tuple (first :: (← parseSeparated fuel ")" (parsePattern fuel)))
        let _ ← expect ")"
        return first
      if ← accept "[" then
        let rec array : Nat → List Pattern → List Pattern → Option Id → ParseM Pattern
          | 0, _, _, _ => reject .resourceLimit "array pattern parser exhausted"
          | fuel + 1, before, after, rest => do
            if ← accept "]" then return .array before after rest
            if ← accept ".." then
              require rest.isNone .invalidSource "array pattern has more than one remainder"
              let id ← parserId
              let _ ← accept ","
              array fuel before after (some id)
            else
              let pattern ← parsePattern fuel
              let before := if rest.isNone then before ++ [pattern] else before
              let after := if rest.isSome then after ++ [pattern] else after
              if ← accept "," then array fuel before after rest else
                let _ ← expect "]"
                return .array before after rest
        return ← array fuel [] [] none
      let token ← peek
      match token.kind with
      | .number _ | .character .. => return .constant (← parseTerm fuel .constant)
      | .identifier _ =>
        let path ← parsePath fuel
        if ← accept "(" then return .named path (← parseSeparated fuel ")" (parsePattern fuel))
        if ← accept "{" then
          let rec fields : Nat → List (String × Pattern) → Bool → ParseM Pattern
            | 0, _, _ => reject .resourceLimit "record pattern parser exhausted"
            | fuel + 1, values, rest => do
              if ← accept "}" then return .record path values rest
              if ← accept ".." then
                require (!rest) .invalidSource "record pattern has repeated remainder"
                let _ ← accept ","
                fields fuel values true
              else
                let (name, _) ← identifier
                let pattern ← if ← accept ":" then parsePattern fuel else pure (.binder (← parserId) name false)
                if ← accept "," then fields fuel (values ++ [(name, pattern)]) rest else
                  let _ ← expect "}"
                  return .record path (values ++ [(name, pattern)]) rest
          return ← fields fuel [] false
        match path.components with
        | [name] => return .binder (← parserId) name false
        | _ => return .named path []
      | _ => reject .invalidSource "invalid structural pattern" token.span

  def parseExpr (fuel : Nat) (stop : List String := []) : ParseM Expr := do
    match fuel with
    | 0 => reject .resourceLimit "expression parser exhausted"
    | fuel + 1 =>
      let firstSpan := (← peek).span
      let rec chain : Nat → List ChainPart → Bool → ParseM Expr
        | 0, _, _ => reject .resourceLimit "operator-chain parser exhausted"
        | fuel + 1, parts, needOperand => do
          let token ← peek
          if stop.contains token.spelling || [";", ",", ")", "]", "}", "=>", "<eof>"].contains token.spelling then
            require (!needOperand && !parts.isEmpty) .invalidSource "expression is missing an operand" token.span
            match parts with | [.operand value] => return value | _ => return .operatorChain firstSpan parts
          if needOperand then
            if ["-", "+", "~"].contains token.spelling then
              let _ ← takeToken
              chain fuel (parts ++ [.operator token.spelling token.span]) true
            else
              let value ← parsePostfix fuel (← parseAtom fuel)
              chain fuel (parts ++ [.operand value]) false
          else
            if token.spelling == "is" then
              let _ ← takeToken
              let pattern ← parsePattern fuel
              let subject := match parts with | [.operand value] => value | _ => Expr.operatorChain firstSpan parts
              chain fuel [.operand (.test firstSpan subject pattern)] false
            else if ["=", ":", "{"].contains token.spelling then
              match parts with | [.operand value] => return value | _ => return .operatorChain firstSpan parts
            else
              let _ ← takeToken
              chain fuel (parts ++ [.operator token.spelling token.span]) true
      chain fuel [] true

  def parsePostfix (fuel : Nat) (expression : Expr) : ParseM Expr := do
    match fuel with
    | 0 => reject .resourceLimit "application parser exhausted"
    | fuel + 1 =>
      if ← accept "(" then
        let arguments ← parseSeparated fuel ")" (parseExpr fuel)
        parsePostfix fuel (.apply expression.span expression arguments)
      else if ← accept "." then
        let token ← takeToken
        let index ← getRequired token.spelling.toNat? .invalidSource "numeric projection requires a field number" token.span
        parsePostfix fuel (.project expression.span expression (.field index))
      else if (← peek).spelling == "{" then
        let block ← parseBlock fuel
        let application := match expression with
          | .apply span callee arguments => Expr.apply span callee (arguments ++ [block])
          | _ => .apply expression.span expression [block]
        parsePostfix fuel application
      else return expression

  def parseAtom (fuel : Nat) : ParseM Expr := do
    match fuel with
    | 0 => reject .resourceLimit "atomic expression parser exhausted"
    | fuel + 1 =>
      let token ← peek
      if ← accept "(" then
        if ← accept ")" then return .unit token.span
        let first ← parseExpr fuel
        if ← accept "," then return .tuple token.span (first :: (← parseSeparated fuel ")" (parseExpr fuel)))
        let _ ← expect ")"
        return first
      if ← accept "[" then return .array token.span (← parseSeparated fuel "]" (parseExpr fuel))
      if token.spelling == "{" then return ← parseBlock fuel
      if ← accept "&" then
        let mode := if ← accept "mut" then Mutability.unique else .shared
        return .borrow token.span mode (← parsePostfix fuel (← parseAtom fuel))
      if ← accept "*" then return .project token.span (← parsePostfix fuel (← parseAtom fuel)) .dereference
      if ← accept "move" then return .move token.span (← parsePostfix fuel (← parseAtom fuel))
      if ← accept "unsafe" then return .unsafeScope token.span (← parseBlock fuel)
      if ← accept "tail" then
        let invocation ← parsePostfix fuel (← parseAtom fuel)
        match invocation with
        | .apply _ callee arguments => return .tail token.span callee arguments
        | _ => reject .invalidSource "tail requires an application" token.span
      if ← accept "fn" then
        let identity : DeclId := ⟨(← get).module.packageId, ← parserId⟩
        let parameters ← parseParameters fuel false
        let output ← if ← accept "->" then pure (some (← parseTerm fuel)) else pure none
        let effects ← if ← accept "/" then pure (some (← parseRow fuel)) else pure none
        let body ← parseBlock fuel
        return .lambda token.span identity parameters output effects body []
      if ← accept "handle" then
        let body ← parseExpr fuel ["{"]
        let _ ← expect "{"
        let clauses ← parseHandlerArms fuel
        return .handle token.span body clauses
      match token.kind with
      | .number spelling =>
        let _ ← takeToken
        return .literal token.span (← numericLiteral spelling token.span)
      | .character scalar byte =>
        let _ ← takeToken
        return .literal token.span (if byte then .integer scalar (some (.integer false .w8)) false else .character scalar)
      | .string bytes byte =>
        let _ ← takeToken
        return .literal token.span (if byte then .bytes bytes else .text bytes)
      | .label name =>
        let _ ← takeToken
        if (← peek).spelling == "{" || (← peek).spelling == ":" then
          let type ← if ← accept ":" then pure (some (← parseTerm fuel)) else pure none
          return .label token.span (← parserId) name type (← parseBlock fuel)
        return .name token.span ⟨["@" ++ name]⟩ []
      | .identifier _ =>
        let path ← parsePath fuel
        let explicit ← if (← peek).spelling == "::" && (← peekAt 1).spelling == "<" then
            let _ ← takeToken; parseGenericArguments fuel
          else if (← peek).spelling == "<" then parseGenericArguments fuel else pure []
        return .name token.span path explicit
      | _ => reject .invalidSource "expected an expression" token.span

  def blockHasArms (fuel : Nat) : ParseM Bool := do
    let state ← get
    let rec inspect : Nat → Nat → Nat → Bool
      | 0, _, _ => false
      | fuel + 1, position, depth =>
        match state.tokens[position]? with
        | none => false
        | some token =>
          if token.spelling == "=>" && depth == 0 then true
          else if token.spelling == "}" && depth == 0 then false
          else if ["{", "(", "["].contains token.spelling then inspect fuel (position + 1) (depth + 1)
          else if ["}", ")", "]"].contains token.spelling then inspect fuel (position + 1) (depth - 1)
          else if token.spelling == ";" && depth == 0 then false
          else inspect fuel (position + 1) depth
    return inspect fuel state.position 0

  def parseBlock (fuel : Nat) : ParseM Expr := do
    match fuel with
    | 0 => reject .resourceLimit "block parser exhausted"
    | fuel + 1 =>
      let opening ← expect "{"
      if ← accept "=>" then
        let body ← parseExpr fuel
        let _ ← expect "}"
        return .lambda opening.span ⟨(← get).module.packageId, ← parserId⟩ [] none none body []
      if ← blockHasArms fuel then
        let clauses ← parseSeparated fuel "}" (do
          let span := (← peek).span
          let pattern ← parsePattern fuel
          let _ ← expect "=>"
          let body ← parseExpr fuel
          pure (PatternClause.clause span pattern body))
        return .patternCallable opening.span ⟨(← get).module.packageId, ← parserId⟩ clauses
      let rec statements : Nat → List Statement → ParseM Expr
        | 0, _ => reject .resourceLimit "statement parser exhausted"
        | fuel + 1, items => do
          if ← accept "}" then return .block opening.span items none
          let token ← peek
          if ← accept "let" then
            let mutable := ← accept "mut"
            let pattern ← parsePattern fuel
            let annotation ← if ← accept ":" then pure (some (← parseTerm fuel)) else pure none
            let _ ← expect "="
            let initializer ← parseExpr fuel
            let _ ← expect ";"
            statements fuel (items ++ [.binding token.span pattern mutable annotation initializer])
          else
            let expression ← parseExpr fuel
            if ← accept "=" then
              let value ← parseExpr fuel
              let _ ← expect ";"
              statements fuel (items ++ [.assign token.span expression value])
            else if ← accept ";" then statements fuel (items ++ [.discard token.span expression])
            else
              let _ ← expect "}"
              return .block opening.span items (some expression)
      statements fuel []

  def parseHandlerArms (fuel : Nat) : ParseM (List HandlerClause) := do
    parseSeparated fuel "}" (do
      let token ← peek
      let pattern ← parsePattern fuel
      let _ ← expect "=>"
      let body ← parseExpr fuel
      match pattern with
      | .named path patterns =>
        -- Resolution classifies heads after all declarations/imports are known.
        let id := (← get).program.effects.findSome? fun effect =>
          effect.operations.find? (fun operation => operation.header.name == path.components.getLast!) |>.map (·.header.id)
        match id with
        | some id => return .operation token.span id [] patterns none body
        | none => return .completion token.span pattern body
      | _ => return .completion token.span pattern body)

  def parseParameters (fuel : Nat) (annotated : Bool) : ParseM (List Parameter) := do
    let _ ← expect "("
    parseSeparated fuel ")" (do
      let mutable := ← accept "mut"
      let (name, span) ← identifier
      let type ← if ← accept ":" then pure (some (← parseTerm fuel)) else pure none
      require (!annotated || type.isSome) .invalidSource "function parameters require declared types" span
      return ⟨← parserId, name, type, mutable⟩)
end

def parseAttributes (fuel : Nat) : ParseM (List (String × List String)) := do
  let rec loop : Nat → List (String × List String) → ParseM (List (String × List String))
    | 0, _ => reject .resourceLimit "attribute parser exhausted"
    | fuel + 1, attributes => do
      if !(← accept "#") then return attributes
      let inner := ← accept "!"
      let _ ← expect "["
      let (name, _) ← identifier
      let arguments ← if ← accept "(" then parseSeparated fuel ")" (return (← takeToken).spelling) else pure []
      let arguments ← if ← accept "=" then pure (arguments ++ [(← takeToken).spelling]) else pure arguments
      let _ ← expect "]"
      if inner && name == "no_implicit_prelude" then
        modify fun state => { state with program.modules := state.program.modules.map (fun m =>
          if m.identity == state.module then { m with noImplicitPrelude := true } else m) }
      loop fuel (attributes ++ [(name, arguments)])
  loop fuel []

mutual
  def parseItems (fuel : Nat) (closing : String := "<eof>") : ParseM Unit := do
    match fuel with
    | 0 => reject .resourceLimit "declaration parser exhausted"
    | fuel + 1 =>
      if ← accept closing then return
      let attributes ← parseAttributes fuel
      let visibility ← parseVisibility
      let unsafe_ := ← accept "unsafe"
      let abi ← if ← accept "extern" then do
          let token ← takeToken
          match token.kind with
          | .string bytes false =>
            require (String.fromUTF8? (ByteArray.mk bytes.toArray) == some "C") .invalidSource "only explicit C foreign ABI is admitted" token.span
            pure ABI.c
          | _ => reject .invalidSource "extern requires a quoted ABI" token.span
        else pure ABI.glorious
      let token ← takeToken
      match token.spelling with
      | "fn" => parseFunction fuel visibility unsafe_ abi attributes
      | "struct" => parseData fuel visibility false attributes
      | "enum" => parseData fuel visibility true attributes
      | "type" =>
        let before := (← get).binders
        let (name, span) ← identifier
        let header ← parserDecl name span visibility
        let generics ← parseBinders fuel
        let _ ← expect "="
        let value ← parseTerm fuel
        let _ ← expect ";"
        modify fun state => { state with binders := before, program.aliases := state.program.aliases ++ [⟨header, generics, value⟩] }
      | "const" | "let" =>
        let before := (← get).binders
        let (name, span) ← identifier
        let header ← parserDecl name span visibility
        let generics ← parseBinders fuel
        let _ ← expect ":"
        let type ← parseTerm fuel
        let _ ← expect "="
        let value ← parseTerm fuel .constant
        let _ ← expect ";"
        modify fun state => { state with
          binders := before,
          program.constants := state.program.constants ++ [⟨header, generics, type, value, token.spelling == "let"⟩] }
      | "effect" => parseEffect fuel visibility
      | "trait" => parseTrait fuel visibility unsafe_
      | "impl" => parseImpl fuel unsafe_
      | "mod" =>
        let (name, _) ← identifier
        let parent := (← get).module
        let child := { parent with path := parent.path ++ [name] }
        modify fun state => { state with program.modules := state.program.modules.map (fun moduleDecl =>
          if moduleDecl.identity == parent then { moduleDecl with children := moduleDecl.children ++ [child] } else moduleDecl) }
        if ← accept ";" then pure () else
          let _ ← expect "{"
          modify fun state => { state with
            module := child,
            program.modules := state.program.modules ++ [⟨child, [], [], false⟩] }
          parseItems fuel "}"
          modify fun state => { state with module := parent }
      | "use" => parseImport fuel visibility
      | "infixl" | "infixr" | "infix" | "prefix" =>
        let precedence ← takeToken
        let precedence ← getRequired precedence.spelling.toNat? .invalidSource "fixity precedence must be an integer" precedence.span
        let spelling ← takeToken
        let target ← if ← accept "=" then parsePath fuel else pure ⟨[spelling.spelling]⟩
        let _ ← expect ";"
        let associativity : Associativity := match token.spelling with
          | "infixl" => .left | "infixr" => .right | "prefix" => .«prefix» | _ => .none
        let fixity : Fixity := ⟨(← get).module, spelling.spelling, associativity, precedence,
          ⟨(← get).module.packageId, 0⟩, token.span, some target⟩
        modify fun state => { state with program.fixities := state.program.fixities ++ [fixity] }
      | "{" =>
        require (abi == .c) .invalidSource "unexpected declaration block" token.span
        parseForeignItems fuel visibility unsafe_
      | _ => reject .invalidSource s!"unsupported declaration syntax: {token.spelling}" token.span
      parseItems fuel closing

  def parseFunction (fuel : Nat) (visibility : Visibility) (unsafe_ : Bool) (abi : ABI)
      (attributes : List (String × List String)) : ParseM Unit := do
    let before ← get
    let (name, span) ← identifier
    let header ← parserDecl name span visibility
    let generics ← parseBinders fuel
    modify fun state => { state with implicitRegions := [], inputRegions := [], parsingResult := false }
    let parameters ← parseParameters fuel true
    modify fun state => { state with parsingResult := true }
    let output ← if ← accept "->" then parseTerm fuel else pure .unit
    let effects ← if ← accept "/" then parseRow fuel else pure (.row [] [])
    let constraints ← parseConstraints fuel
    let signature : Signature := {
      generics := generics ++ (← get).implicitRegions,
      arguments := parameters.map (fun p => p.type.getD .unit), output, effects, constraints, unsafeCall := unsafe_, abi }
    let body ← if ← accept ";" then pure none else pure (some (← parseBlock fuel))
    let exportName := (lookup "export_name" attributes).bind List.head?
    let function : FunctionDecl := { header, signature, parameters, body, exportName, owner := before.currentOwner }
    modify fun state => { state with
      binders := before.binders, implicitRegions := before.implicitRegions,
      inputRegions := before.inputRegions, parsingResult := before.parsingResult,
      program.functions := state.program.functions ++ [function] }

  def parseData (fuel : Nat) (visibility : Visibility) (enumeration : Bool)
      (attributes : List (String × List String)) : ParseM Unit := do
    let before := (← get).binders
    let (name, span) ← identifier
    let header ← parserDecl name span visibility
    let generics ← parseBinders fuel
    let parseFields (named : Bool) : ParseM (List FieldDecl) := do
      let close := if named then "}" else ")"
      parseSeparated fuel close (do
        let visibility ← parseVisibility
        let (name, fieldSpan) ← if named then identifier else pure ("", (← peek).span)
        if named then let _ ← expect ":"; pure ()
        let type ← parseTerm fuel
        let header ← parserDecl name fieldSpan visibility
        return ⟨header, type⟩)
    let variants ← if enumeration then do
        let _ ← expect "{"
        parseSeparated fuel "}" (do
          let (name, span) ← identifier
          let variant ← parserDecl name span .public
          let fields ← if ← accept "(" then parseFields false else if ← accept "{" then parseFields true else pure []
          return (⟨variant, fields⟩ : VariantDecl))
      else do
        let fields ← if ← accept "(" then do
            let fields ← parseFields false
            let _ ← expect ";"
            pure fields
          else if ← accept "{" then parseFields true
          else do let _ ← expect ";"; pure []
        pure [⟨header, fields⟩]
    let representation := match (lookup "repr" attributes).bind List.head? with
      | some "C" => Representation.c | some "transparent" => .transparent
      | some name => match parseScalarType name with | some (.integer signed width) => .integer signed width | _ => .glorious
      | none => .glorious
    let data : DataDecl := {
      header, generics, variants, isEnum := enumeration, representation,
      nonExhaustive := (lookup "non_exhaustive" attributes).isSome }
    modify fun state => { state with binders := before, program.dataTypes := state.program.dataTypes ++ [data] }

  def parseEffect (fuel : Nat) (visibility : Visibility) : ParseM Unit := do
    let before := (← get).binders
    let (name, span) ← identifier
    let header ← parserDecl name span visibility
    let generics ← parseBinders fuel
    let requirements ← parseConstraints fuel
    let _ ← expect "{"
    let rec operations : Nat → List OperationDecl → ParseM (List OperationDecl)
      | 0, _ => reject .resourceLimit "effect declaration parser exhausted"
      | fuel + 1, result => do
        if ← accept "}" then return result
        let quantity ← if ← accept "[" then do
            let lower ← takeToken
            let lower ← getRequired lower.spelling.toNat? .invalidSource "resumption lower bound is not an integer" lower.span
            let _ ← expect ","
            let upper ← if ← accept "*" then pure none else do
              let upper ← takeToken
              pure (some (← getRequired upper.spelling.toNat? .invalidSource "resumption upper bound is not an integer" upper.span))
            let _ ← expect "]"
            pure (some (lower, upper))
          else pure none
        let (name, span) ← identifier
        let operation ← parserDecl name span .public
        let opGenerics ← parseBinders fuel
        let _ ← expect "("
        let arguments ← parseSeparated fuel ")" (parseTerm fuel)
        let output ← if ← accept "->" then parseTerm fuel else pure .unit
        let constraints ← parseConstraints fuel
        let _ ← accept ";"
        let _ ← accept ","
        let declaration : OperationDecl := ⟨operation, { generics := opGenerics, arguments, output, constraints }, quantity⟩
        operations fuel (result ++ [declaration])
    let operations ← operations fuel []
    modify fun state => { state with binders := before, program.effects := state.program.effects ++ [⟨header, generics, requirements, operations⟩] }

  def parseTrait (fuel : Nat) (visibility : Visibility) (unsafe_ : Bool) : ParseM Unit := do
    let before := (← get).binders
    let (name, span) ← identifier
    let header ← parserDecl name span visibility
    let self : Binder := ⟨← parserId, "Self", .type, none⟩
    modify fun state => { state with binders := state.binders ++ [self], selfType := some (.param self.id .type) }
    let generics ← parseBinders fuel
    let supertraits ← parseConstraints fuel
    let _ ← expect "{"
    let rec members : Nat → List TraitMember → ParseM (List TraitMember)
      | 0, _ => reject .resourceLimit "trait member parser exhausted"
      | fuel + 1, result => do
        if ← accept "}" then return result
        let token ← takeToken
        if token.spelling == "type" then
          let (name, span) ← identifier
          let member ← parserDecl name span .public
          let generics ← parseBinders fuel
          let kind ← if ← accept ":" then
              let (name, _) ← identifier
              pure (if name == "EffectRow" then Kind.row else Kind.type)
            else pure Kind.type
          let defaultValue ← if ← accept "=" then pure (some (← parseTerm fuel kind)) else pure none
          let _ ← expect ";"
          members fuel (result ++ [⟨member, generics, kind, defaultValue, none⟩])
        else if token.spelling == "fn" then
          let count := (← get).program.functions.length
          parseFunction fuel .public false .glorious []
          let function ← getRequired (← get).program.functions[count]? .malformedCore "trait method parser lost its declaration"
          modify fun state => { state with program.functions := state.program.functions.map (fun f =>
            if f.header.id == function.header.id then { f with traitMember := some header.id } else f) }
          members fuel (result ++ [⟨function.header, function.signature.generics, .type, none, some function.signature⟩])
        else reject .invalidSource "expected a trait method or associated type" token.span
    let members ← members fuel []
    let declaration : TraitDecl := ⟨header, self :: generics, supertraits, members, false, unsafe_⟩
    modify fun state => { state with binders := before, selfType := none, program.traits := state.program.traits ++ [declaration] }

  def parseImpl (fuel : Nat) (unsafe_ : Bool) : ParseM Unit := do
    let before ← get
    let span := (← peek).span
    let header ← parserDecl s!"impl#{before.nextId}" span .private
    let generics ← parseBinders fuel
    let negative := ← accept "!"
    let head ← parseTerm fuel
    let (traitPath, arguments, self) ← if ← accept "for" then do
        let self ← parseTerm fuel
        match head with
        | .named path arguments _ => pure (some (⟨path⟩ : Path), self :: arguments, self)
        | _ => reject .invalidSource "implementation trait head must name a trait" span
      else pure (none, [], head)
    let requirements ← parseConstraints fuel
    let _ ← expect "{"
    modify fun state => { state with selfType := some self, currentOwner := some self }
    let rec members : Nat → List (DeclId × Term) → List (DeclId × DeclId) → ParseM (List (DeclId × Term) × List (DeclId × DeclId))
      | 0, _, _ => reject .resourceLimit "implementation body parser exhausted"
      | fuel + 1, associated, methods => do
        if ← accept "}" then return (associated, methods)
        let visibility ← parseVisibility
        let unsafeMethod := ← accept "unsafe"
        let token ← takeToken
        if token.spelling == "fn" then
          let count := (← get).program.functions.length
          parseFunction fuel visibility unsafeMethod .glorious []
          let function ← getRequired (← get).program.functions[count]? .malformedCore "impl method parser lost its declaration"
          members fuel associated (methods ++ [(function.header.id, function.header.id)])
        else if token.spelling == "type" then
          let (name, span) ← identifier
          let member ← parserDecl name span .public
          let _ ← expect "="
          let value ← parseTerm fuel
          let _ ← expect ";"
          members fuel (associated ++ [(member.id, value)]) methods
        else reject .invalidSource "expected an implementation method or associated definition" token.span
    let (associated, methods) ← members fuel [] []
    let declaration : ImplDecl := {
      header, generics, traitDecl := ⟨before.module.packageId, 0⟩,
      arguments, requirements, associated, methods, negative, unsafeImpl := unsafe_, traitPath }
    modify fun state => { state with
      binders := before.binders, selfType := before.selfType, currentOwner := before.currentOwner,
      program.implementations := if traitPath.isSome then state.program.implementations ++ [declaration] else state.program.implementations }

  def parseImport (fuel : Nat) (visibility : Visibility) : ParseM Unit := do
    let module := (← get).module
    let rec tree : Nat → List String → ParseM (List Import)
      | 0, _ => reject .resourceLimit "import tree parser exhausted"
      | fuel + 1, earlier => do
        if ← accept "{" then
          return (← parseSeparated fuel "}" (tree fuel earlier)).flatten
        if ← accept "*" then
          return [⟨module, ⟨earlier⟩, .value, none, true, false, visibility == .public, false, {}⟩]
        let (name, span) ← identifier
        let names := earlier ++ [name]
        if ← accept "::" then tree fuel names else
          let aliasName ← if ← accept "as" then pure (some (← identifier).1) else pure none
          return [⟨module, ⟨names⟩, .value, aliasName, false, false, visibility == .public, true, span⟩]
    let imports ← tree fuel []
    let _ ← expect ";"
    modify fun state => { state with program.modules := state.program.modules.map (fun m =>
      if m.identity == module then { m with imports := m.imports ++ imports } else m) }

  def parseForeignItems (fuel : Nat) (visibility : Visibility) (unsafe_ : Bool) : ParseM Unit := do
    match fuel with
    | 0 => reject .resourceLimit "foreign declaration block parser exhausted"
    | fuel + 1 =>
      if ← accept "}" then return
      let _ ← expect "fn"
      parseFunction fuel visibility true .c []
      parseForeignItems fuel visibility unsafe_
end

def parseFiles (initial : Program) (files : List SourceFile) : Check Program := do
  let (_, program) ← files.foldlM (init := (1, initial)) fun (nextId, program) file => do
    let tokens ← lex file
    let program := if program.modules.any (fun moduleDecl => moduleDecl.identity == file.module) then program else
      { program with modules := program.modules ++ [⟨file.module, [], [], false⟩] }
    let state : ParserState := { tokens, nextId, module := file.module, program }
    let (_, state) ← (parseItems (tokens.size * 8 + 1)).run state
    return (state.nextId, state.program)
  return program

end Glorious.Semantics
