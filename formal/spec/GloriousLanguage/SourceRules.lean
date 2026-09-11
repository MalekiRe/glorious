import GloriousLanguage.Syntax

/-! The source grammar is indexed by the syntax it denotes. There is no
separate unconnected parse tree whose acceptance could validate an invented
AST. Delimiters and tuple arity survive until contextual elaboration. -/
namespace Glorious.Language.Source

abbrev Tokens := List Token
private def s := Token.symbol
private def w := Token.word
private def n := Token.name

inductive PathSyntax : Tokens → Path → Prop where
  | one {name} : name ≠ "_" → PathSyntax [n name] [name]
  | more {name tokens path} : name ≠ "_" → PathSyntax tokens path → PathSyntax (n name :: s "::" :: tokens) (name :: path)

def NaturalToken (token : Token) (value : Nat) : Prop :=
  ∃ literal, token = .literal (.integer literal) ∧ literal.suffix = none ∧ value = digitsValue literal.base literal.digits

inductive QuantitySyntax : Tokens → Quantity → Prop where
  | finite {a b lower upper} : NaturalToken a lower → NaturalToken b upper → lower ≤ upper →
      QuantitySyntax [s "[",a,s ",",b,s "]"] ⟨lower,some upper⟩
  | unbounded {a lower} : NaturalToken a lower → QuantitySyntax [s "[",a,s ",",s "*",s "]"] ⟨lower,none⟩

mutual
  inductive TypeSyntax : Tokens → TypeExpr → Prop where
    | infer : TypeSyntax [n "_"] .infer
    | unit : TypeSyntax [s "(",s ")"] .unit
    | bottom : TypeSyntax [s "!"] .bottom
    | grouping {tokens type} : TypeSyntax tokens type → TypeSyntax (s "(" :: tokens ++ [s ")"]) type
    | tuple {first rest firstTokens restTokens} : TypeSyntax firstTokens first → TypesSyntax restTokens rest →
        TypeSyntax (s "(" :: firstTokens ++ s "," :: restTokens ++ [s ")"]) (.tuple (first :: rest))
    | array {element length elementTokens lengthTokens} : TypeSyntax elementTokens element → TypeSyntax lengthTokens length →
        TypeSyntax (s "[" :: elementTokens ++ s ";" :: lengthTokens ++ [s "]"]) (.array element length)
    | path {path pathTokens arguments argumentTokens} : PathSyntax pathTokens path → ArgumentsSyntax argumentTokens arguments →
        TypeSyntax (pathTokens ++ argumentTokens) (.path path arguments [])
    | item {path pathTokens owners ownerTokens member items itemTokens} : PathSyntax pathTokens path →
        ArgumentsSyntax ownerTokens owners → ArgumentsSyntax itemTokens items →
        TypeSyntax (pathTokens ++ ownerTokens ++ [s "::",n member] ++ itemTokens) (.path (path ++ [member]) owners items)
    | reference {mode region type tokens prefixTokens} : ReferencePrefix prefixTokens mode region → TypeSyntax tokens type →
        TypeSyntax (prefixTokens ++ tokens) (.reference mode region type)
    | pointerShared {type tokens} : TypeSyntax tokens type → TypeSyntax (s "*" :: w "const" :: tokens) (.pointer .shared type)
    | pointerUnique {type tokens} : TypeSyntax tokens type → TypeSyntax (s "*" :: w "mut" :: tokens) (.pointer .unique type)
    | lifetime {name} : TypeSyntax [.lifetime name] (.lifetime name)
    | constant {literal} : TypeSyntax [.literal literal] (.constant literal)
    | quantity {tokens quantity} : QuantitySyntax tokens quantity → TypeSyntax tokens (.quantity quantity)
    | binding {name tokens value} : TypeSyntax tokens value → TypeSyntax (n name :: s "=" :: tokens) (.binding name value)
    | constructor {path pathTokens arguments argumentTokens fields fieldTokens} : PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments → TypesSyntax fieldTokens fields →
        TypeSyntax (pathTokens ++ argumentTokens ++ s "(" :: fieldTokens ++ [s ")"]) (.constructor path arguments fields)
    | row {instances tails first rest} : TypesSyntax first instances → RowTailSyntax rest tails →
        TypeSyntax (s "{" :: first ++ rest ++ [s "}"]) (.row instances tails)
    | associated {owner ownerTokens trait traitTokens traitArguments traitArgumentTokens member arguments argumentTokens} :
        TypeSyntax ownerTokens owner → PathSyntax traitTokens trait → ArgumentsSyntax traitArgumentTokens traitArguments →
        ArgumentsSyntax argumentTokens arguments →
        TypeSyntax (s "<" :: ownerTokens ++ n "as" :: traitTokens ++ traitArgumentTokens ++ [s ">",s "::",n member] ++ argumentTokens)
          (.associated owner trait traitArguments member arguments)

  inductive TypesSyntax : Tokens → List TypeExpr → Prop where
    | nil : TypesSyntax [] []
    | one {tokens type} : TypeSyntax tokens type → TypesSyntax tokens [type]
    | cons {first rest type types} : TypeSyntax first type → TypesSyntax rest types →
        TypesSyntax (first ++ s "," :: rest) (type :: types)

  inductive ArgumentsSyntax : Tokens → List TypeExpr → Prop where
    | absent : ArgumentsSyntax [] []
    | explicit {tokens arguments} : TypesSyntax tokens arguments → ArgumentsSyntax (s "<" :: tokens ++ [s ">"]) arguments

  inductive RowTailSyntax : Tokens → List TypeExpr → Prop where
    | absent : RowTailSyntax [] []
    | tails {tokens tails} : tails ≠ [] → TypesSyntax tokens tails → RowTailSyntax (s "|" :: tokens) tails

  inductive ReferencePrefix : Tokens → Mutability → Option String → Prop where
    | shared : ReferencePrefix [s "&"] .shared none
    | unique : ReferencePrefix [s "&",w "mut"] .unique none
    | sharedRegion {region} : ReferencePrefix [s "&",.lifetime region] .shared (some region)
    | uniqueRegion {region} : ReferencePrefix [s "&",.lifetime region,w "mut"] .unique (some region)
end

inductive VisibilitySyntax : Tokens → Visibility → Prop where
  | privateScope : VisibilitySyntax [] .privateScope
  | publicScope : VisibilitySyntax [w "pub"] .publicScope
  | package : VisibilitySyntax [w "pub",s "(",n "crate",s ")"] .package
  | parent : VisibilitySyntax [w "pub",s "(",n "super",s ")"] .parent

inductive OptionalTypeSyntax : Tokens → Option TypeExpr → Prop where
  | absent : OptionalTypeSyntax [] none
  | annotation {tokens type} : TypeSyntax tokens type → OptionalTypeSyntax (s ":" :: tokens) (some type)

inductive DefaultSyntax : Tokens → Option TypeExpr → Prop where
  | absent : DefaultSyntax [] none
  | value {tokens type} : TypeSyntax tokens type → DefaultSyntax (s "=" :: tokens) (some type)

inductive GenericSyntax : Tokens → Generic → Prop where
  | type {name tokens value} : DefaultSyntax tokens value → GenericSyntax (n name :: tokens) ⟨name,.type,value,none⟩
  | region {name tokens value} : DefaultSyntax tokens value → GenericSyntax (.lifetime name :: tokens) ⟨name,.region,value,none⟩
  | row {name tokens value} : DefaultSyntax tokens value →
      GenericSyntax (n name :: s ":" :: n "EffectRow" :: tokens) ⟨name,.row,value,none⟩
  | constant {name typeTokens type tokens value} : TypeSyntax typeTokens type → DefaultSyntax tokens value →
      GenericSyntax (w "const" :: n name :: s ":" :: typeTokens ++ tokens) ⟨name,.constant,value,some type⟩

inductive GenericListSyntax : Tokens → List Generic → Prop where
  | nil : GenericListSyntax [] []
  | one {tokens generic} : GenericSyntax tokens generic → GenericListSyntax tokens [generic]
  | cons {first rest generic generics} : GenericSyntax first generic → GenericListSyntax rest generics →
      GenericListSyntax (first ++ s "," :: rest) (generic :: generics)

inductive GenericsSyntax : Tokens → List Generic → Prop where
  | absent : GenericsSyntax [] []
  | explicit {tokens generics} : generics ≠ [] → GenericListSyntax tokens generics →
      GenericsSyntax (s "<" :: tokens ++ [s ">"]) generics

mutual
  inductive PredicateSyntax : Tokens → Predicate → Prop where
    | equal {left right a b} : TypeSyntax left a → TypeSyntax right b → PredicateSyntax (left ++ s "=" :: right) (.equal a b)
    | outlives {left a region} : TypeSyntax left a → PredicateSyntax (left ++ [s ":",.lifetime region]) (.outlives a (.lifetime region))
    | bound {left subject pathTokens path argumentTokens arguments} : TypeSyntax left subject → PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments →
        PredicateSyntax (left ++ s ":" :: pathTokens ++ argumentTokens) (.bound subject path arguments false false)
    | unsafeBound {left subject pathTokens path argumentTokens arguments} : TypeSyntax left subject → PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments →
        PredicateSyntax (left ++ [s ":",w "unsafe"] ++ pathTokens ++ argumentTokens) (.bound subject path arguments true false)
    | negativeBound {left subject pathTokens path argumentTokens arguments} : TypeSyntax left subject → PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments →
        PredicateSyntax (left ++ [s ":",s "!"] ++ pathTokens ++ argumentTokens) (.bound subject path arguments false true)
    | quantified {binderTokens binders tokens requirements} : GenericListSyntax binderTokens binders →
        PredicatesSyntax tokens requirements →
        PredicateSyntax ([n "for",s "<"] ++ binderTokens ++ [s ">"] ++ tokens)
          (.quantified (binders.map (fun binder => (binder.name,binder.kind))) requirements)

  inductive PredicatesSyntax : Tokens → List Predicate → Prop where
    | nil : PredicatesSyntax [] []
    | one {tokens predicate} : PredicateSyntax tokens predicate → PredicatesSyntax tokens [predicate]
    | cons {first rest predicate predicates} : PredicateSyntax first predicate → PredicatesSyntax rest predicates →
        PredicatesSyntax (first ++ s "," :: rest) (predicate :: predicates)
    | bounds {left subject first rest path arguments safe negative predicates} :
        TypeSyntax left subject → PredicateSyntax (left ++ s ":" :: first) (.bound subject path arguments safe negative) →
        PredicatesSyntax (left ++ s ":" :: rest) predicates →
        PredicatesSyntax (left ++ s ":" :: first ++ s "+" :: rest) (.bound subject path arguments safe negative :: predicates)
end

inductive WhereSyntax : Tokens → List Predicate → Prop where
  | absent : WhereSyntax [] []
  | requirements {tokens requirements} : requirements ≠ [] → PredicatesSyntax tokens requirements →
      WhereSyntax (w "where" :: tokens) requirements

mutual
  inductive PatternSyntax : Tokens → Pattern → Prop where
    | wildcard : PatternSyntax [n "_"] .wildcard
    | binder {name} : name ≠ "_" → PatternSyntax [n name] (.binder name false)
    | explicitBinder {name} : name ≠ "_" → PatternSyntax [w "let",n name] (.binder name true)
    | constant {path pathTokens arguments argumentTokens} : PathSyntax pathTokens path → ArgumentsSyntax argumentTokens arguments →
        PatternSyntax (pathTokens ++ argumentTokens) (.constant path arguments)
    | literal {literal} : PatternSyntax [.literal literal] (.literal literal)
    | grouping {tokens pattern} : PatternSyntax tokens pattern → PatternSyntax (s "(" :: tokens ++ [s ")"]) pattern
    | unit : PatternSyntax [s "(",s ")"] (.tuple [] none)
    | tuple {tokens patterns remainder} : PatternsSyntax tokens patterns remainder →
        (patterns.length ≠ 1 ∨ s "," ∈ tokens) →
        PatternSyntax (s "(" :: tokens ++ [s ")"]) (.tuple patterns remainder)
    | array {tokens patterns remainder} : PatternsSyntax tokens patterns remainder →
        PatternSyntax (s "[" :: tokens ++ [s "]"]) (.array patterns remainder)
    | constructor {path pathTokens arguments argumentTokens patterns patternTokens remainder} : PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments → PatternsSyntax patternTokens patterns remainder →
        PatternSyntax (pathTokens ++ argumentTokens ++ s "(" :: patternTokens ++ [s ")"]) (.constructor path arguments patterns remainder)
    | record {path pathTokens arguments argumentTokens fields fieldTokens remainder} : PathSyntax pathTokens path →
        ArgumentsSyntax argumentTokens arguments → PatternFieldsSyntax fieldTokens fields remainder →
        PatternSyntax (pathTokens ++ argumentTokens ++ s "{" :: fieldTokens ++ [s "}"]) (.record path arguments fields remainder)
    | shared {tokens pattern} : PatternSyntax tokens pattern → PatternSyntax (s "&" :: tokens) (.reference .shared pattern)
    | unique {tokens pattern} : PatternSyntax tokens pattern → PatternSyntax (s "&" :: w "mut" :: tokens) (.reference .unique pattern)

  inductive PatternsSyntax : Tokens → List Pattern → Option Nat → Prop where
    | nil : PatternsSyntax [] [] none
    | one {tokens pattern} : PatternSyntax tokens pattern → PatternsSyntax tokens [pattern] none
    | cons {first rest pattern patterns remainder} : PatternSyntax first pattern → PatternsSyntax rest patterns remainder →
        PatternsSyntax (first ++ s "," :: rest) (pattern :: patterns) (remainder.map (·+1))
    | remainder : PatternsSyntax [s ".."] [] (some 0)
    | remainderBefore {tokens patterns} : PatternsSyntax tokens patterns none →
        PatternsSyntax (s ".." :: s "," :: tokens) patterns (some 0)

  inductive PatternFieldsSyntax : Tokens → List (String × Pattern) → Bool → Prop where
    | nil : PatternFieldsSyntax [] [] false
    | remainder : PatternFieldsSyntax [s ".."] [] true
    | remainderComma : PatternFieldsSyntax [s "..",s ","] [] true
    | shorthand {name} : name ≠ "_" → PatternFieldsSyntax [n name] [(name,.binder name false)] false
    | one {name tokens pattern} : PatternSyntax tokens pattern → PatternFieldsSyntax (n name :: s ":" :: tokens) [(name,pattern)] false
    | cons {name first rest pattern fields remainder} : PatternSyntax first pattern → PatternFieldsSyntax rest fields remainder →
        PatternFieldsSyntax (n name :: s ":" :: first ++ s "," :: rest) ((name,pattern) :: fields) remainder
    | shorthandCons {name rest fields remainder} : PatternFieldsSyntax rest fields remainder →
        PatternFieldsSyntax (n name :: s "," :: rest) ((name,.binder name false) :: fields) remainder
end

inductive ParameterSyntax : Tokens → Parameter → Prop where
  | parameter {patternTokens typeTokens pattern type} : PatternSyntax patternTokens pattern → TypeSyntax typeTokens type →
      ParameterSyntax (patternTokens ++ s ":" :: typeTokens) ⟨pattern,type⟩

inductive ParametersSyntax : Tokens → List Parameter → Prop where
  | nil : ParametersSyntax [] []
  | one {tokens parameter} : ParameterSyntax tokens parameter → ParametersSyntax tokens [parameter]
  | cons {first rest parameter parameters} : ParameterSyntax first parameter → ParametersSyntax rest parameters →
      ParametersSyntax (first ++ s "," :: rest) (parameter :: parameters)

inductive ResultSyntax : Tokens → TypeExpr → Prop where
  | absent : ResultSyntax [] .unit
  | explicit {tokens type} : TypeSyntax tokens type → ResultSyntax (s "->" :: tokens) type

inductive EffectsSyntax : Tokens → TypeExpr → Prop where
  | absent : EffectsSyntax [] (.row [] [])
  | explicit {tokens type} : TypeSyntax tokens type → EffectsSyntax (s "/" :: tokens) type

inductive FunctionHeadSyntax : Tokens → FunctionHead → Prop where
  | plain {name genericTokens generics parameterTokens parameters resultTokens result effectTokens effects whereTokens requirements} :
      GenericsSyntax genericTokens generics → ParametersSyntax parameterTokens parameters → ResultSyntax resultTokens result →
      EffectsSyntax effectTokens effects → WhereSyntax whereTokens requirements →
      FunctionHeadSyntax ([w "fn",n name] ++ genericTokens ++ s "(" :: parameterTokens ++ [s ")"] ++ resultTokens ++ effectTokens ++ whereTokens)
        ⟨name,generics,parameters,result,effects,requirements,false,false⟩
  | anonymous {parameterTokens parameters resultTokens result effectTokens effects} :
      ParametersSyntax parameterTokens parameters → ResultSyntax resultTokens result → EffectsSyntax effectTokens effects →
      FunctionHeadSyntax ([w "fn",s "("] ++ parameterTokens ++ [s ")"] ++ resultTokens ++ effectTokens)
        ⟨"",[],parameters,result,effects,[],false,false⟩
  | unsafeAllowed {tokens head} : FunctionHeadSyntax tokens head → head.unsafeAllowed = false →
      FunctionHeadSyntax (w "unsafe" :: tokens) { head with unsafeAllowed := true }
  | cABI {tokens head} : FunctionHeadSyntax tokens head → head.cABI = false →
      FunctionHeadSyntax ([w "extern",.literal (.string (text "C"))] ++ tokens) { head with cABI := true }

inductive FieldSyntax : Tokens → Field → Prop where
  | tuple {visibilityTokens visibility typeTokens type} : VisibilitySyntax visibilityTokens visibility → TypeSyntax typeTokens type →
      FieldSyntax (visibilityTokens ++ typeTokens) ⟨none,type,visibility⟩
  | record {visibilityTokens visibility name typeTokens type} : VisibilitySyntax visibilityTokens visibility → TypeSyntax typeTokens type →
      FieldSyntax (visibilityTokens ++ n name :: s ":" :: typeTokens) ⟨some name,type,visibility⟩

inductive FieldsSyntax : Tokens → List Field → Prop where
  | nil : FieldsSyntax [] []
  | one {tokens field} : FieldSyntax tokens field → FieldsSyntax tokens [field]
  | cons {first rest field fields} : FieldSyntax first field → FieldsSyntax rest fields →
      FieldsSyntax (first ++ s "," :: rest) (field :: fields)

inductive VariantSyntax : Tokens → Variant → Prop where
  | unit {name} : VariantSyntax [n name] ⟨name,[],false⟩
  | tuple {name tokens fields} : FieldsSyntax tokens fields → (∀ field ∈ fields, field.name = none) →
      VariantSyntax (n name :: s "(" :: tokens ++ [s ")"]) ⟨name,fields,false⟩
  | record {name tokens fields} : FieldsSyntax tokens fields → (∀ field ∈ fields, field.name.isSome = true) →
      VariantSyntax (n name :: s "{" :: tokens ++ [s "}"]) ⟨name,fields,true⟩

inductive VariantsSyntax : Tokens → List Variant → Prop where
  | nil : VariantsSyntax [] []
  | one {tokens variant} : VariantSyntax tokens variant → VariantsSyntax tokens [variant]
  | cons {first rest variant variants} : VariantSyntax first variant → VariantsSyntax rest variants →
      VariantsSyntax (first ++ s "," :: rest) (variant :: variants)

inductive OptionalQuantitySyntax : Tokens → Option Quantity → Prop where
  | absent : OptionalQuantitySyntax [] none
  | explicit {tokens quantity} : QuantitySyntax tokens quantity → OptionalQuantitySyntax tokens (some quantity)

inductive OperationSyntax : Tokens → Operation → Prop where
  | operation {name quantityTokens quantity genericTokens generics payloadTokens payload resultTokens result whereTokens requirements} :
      OptionalQuantitySyntax quantityTokens quantity → GenericsSyntax genericTokens generics → TypesSyntax payloadTokens payload →
      ResultSyntax resultTokens result → WhereSyntax whereTokens requirements →
      OperationSyntax (quantityTokens ++ n name :: genericTokens ++ s "(" :: payloadTokens ++ [s ")"] ++ resultTokens ++ whereTokens)
        ⟨name,generics,payload,result,quantity,requirements⟩

inductive OperationsSyntax : Tokens → List Operation → Prop where
  | nil : OperationsSyntax [] []
  | cons {first rest operation operations separator} : OperationSyntax first operation → OperationsSyntax rest operations →
      separator = s ";" ∨ separator = s "," →
      OperationsSyntax (first ++ separator :: rest) (operation :: operations)

mutual
  inductive ImportSyntax : Tokens → ImportTree → Prop where
    | name {tokens path} : PathSyntax tokens path → ImportSyntax tokens (.name path none)
    | rename {tokens path name} : PathSyntax tokens path → ImportSyntax (tokens ++ [n "as",n name]) (.name path (some name))
    | glob {tokens path} : PathSyntax tokens path → ImportSyntax (tokens ++ [s "::",s "*"]) (.glob path)
    | group {pathTokens path tokens children} : PathSyntax pathTokens path → ImportsSyntax tokens children →
        ImportSyntax (pathTokens ++ [s "::",s "{"] ++ tokens ++ [s "}"]) (.group path children)
    | rootGroup {tokens children} : ImportsSyntax tokens children → ImportSyntax (s "{" :: tokens ++ [s "}"]) (.group [] children)

  inductive ImportsSyntax : Tokens → List ImportTree → Prop where
    | one {tokens tree} : ImportSyntax tokens tree → ImportsSyntax tokens [tree]
    | cons {first rest tree trees} : ImportSyntax first tree → ImportsSyntax rest trees →
        ImportsSyntax (first ++ s "," :: rest) (tree :: trees)
    | trailing {tokens tree} : ImportSyntax tokens tree → ImportsSyntax (tokens ++ [s ","]) [tree]
end

inductive AttributeSyntax : Tokens → Attribute → Prop where
  | c : AttributeSyntax [n "repr",s "(",n "C",s ")"] .reprC
  | transparent : AttributeSyntax [n "repr",s "(",n "transparent",s ")"] .transparent
  | integer {signed width spelling} : IntegerSuffix (some (.integer signed width)) (text spelling) →
      AttributeSyntax [n "repr",s "(",n spelling,s ")"] (.reprInteger signed width)
  | nonExhaustive : AttributeSyntax [n "non_exhaustive"] .nonExhaustive
  | exportedName {name} : AttributeSyntax [n "export_name",s "=",.literal (.string (text name))] (.exportName name)
  | noStd : AttributeSyntax [n "no_std"] .noStd
  | noPrelude : AttributeSyntax [n "no_implicit_prelude"] .noPrelude

inductive AttributesSyntax : Tokens → List Attribute → Prop where
  | nil : AttributesSyntax [] []
  | annotationEntry {first rest annotationEntry attributes} : AttributeSyntax first annotationEntry → AttributesSyntax rest attributes →
      AttributesSyntax ([s "#",s "["] ++ first ++ [s "]"] ++ rest) (annotationEntry :: attributes)
  | inner {first rest annotationEntry attributes} : AttributeSyntax first annotationEntry → AttributesSyntax rest attributes →
      (annotationEntry = .noStd ∨ annotationEntry = .noPrelude) →
      AttributesSyntax ([s "#",s "!",s "["] ++ first ++ [s "]"] ++ rest) (annotationEntry :: attributes)

inductive Form where
  | atom | postfix | prefixForm | full
  deriving DecidableEq, BEq, Repr, Inhabited

def OperatorToken (token : Token) (operator : String) : Prop :=
  (token = n operator ∧ operator ∉ ["as","for"]) ∨
  (token = s operator ∧ operator ∉ ["=","->","=>","::",".","..",",",";",":","(",")","[","]","{","}","#"])

mutual
  inductive ExpressionSyntax : Form → Tokens → Expr → Prop where
    | literal {literal} : ExpressionSyntax .atom [.literal literal] (.literal literal)
    | unit : ExpressionSyntax .atom [s "(",s ")"] .unit
    | name {path pathTokens owners ownerTokens} : PathSyntax pathTokens path → ArgumentsSyntax ownerTokens owners →
        ExpressionSyntax .atom (pathTokens ++ ownerTokens) (.name path owners [])
    | item {path pathTokens owners ownerTokens member items itemTokens} : PathSyntax pathTokens path →
        ArgumentsSyntax ownerTokens owners → ArgumentsSyntax itemTokens items →
        ExpressionSyntax .atom (pathTokens ++ ownerTokens ++ [s "::",n member] ++ itemTokens) (.name (path ++ [member]) owners items)
    | labelName {name} : ExpressionSyntax .atom [.label name] (.labelName name)
    | grouped {tokens expression} : ExpressionSyntax .full tokens expression →
        ExpressionSyntax .atom (s "(" :: tokens ++ [s ")"]) expression
    | tuple {first rest expression expressions} : ExpressionSyntax .full first expression → ExpressionsSyntax rest expressions →
        ExpressionSyntax .atom (s "(" :: first ++ s "," :: rest ++ [s ")"]) (.tuple (expression :: expressions))
    | array {tokens expressions} : ExpressionsSyntax tokens expressions →
        ExpressionSyntax .atom (s "[" :: tokens ++ [s "]"]) (.array expressions)
    | block {tokens statements result} : BlockSyntax tokens statements result →
        ExpressionSyntax .atom tokens (.block statements result)
    | function {headTokens head bodyTokens body} : FunctionHeadSyntax headTokens head → head.name = "" →
        BlockExpressionSyntax bodyTokens body → ExpressionSyntax .atom (headTokens ++ bodyTokens) (.function head body)
    | zeroFunction {tokens body} : ExpressionSyntax .full tokens body →
        ExpressionSyntax .atom ([s "{",s "=>"] ++ tokens ++ [s "}"])
          (.function ⟨"",[],[],.infer,.row [] [],[],false,false⟩ body)
    | clauses {tokens arms} : arms ≠ [] → ArmsSyntax tokens arms →
        ExpressionSyntax .atom (s "{" :: tokens ++ [s "}"]) (.clauses arms)
    | capture {placeTokens places bodyTokens body} : ExpressionsSyntax placeTokens places →
        ExpressionSyntax .atom bodyTokens body →
        (∃ head value, body = .function head value ∨ ∃ arms, body = .clauses arms ∨ ∃ statements result, body = .block statements result) →
        ExpressionSyntax .atom ([w "move",s "("] ++ placeTokens ++ [s ")"] ++ bodyTokens) (.capture places body)
    | atomic {tokens expression} : ExpressionSyntax .atom tokens expression → ExpressionSyntax .postfix tokens expression
    | call {calleeTokens callee argumentTokens arguments} : ExpressionSyntax .postfix calleeTokens callee →
        ExpressionsSyntax argumentTokens arguments →
        ExpressionSyntax .postfix (calleeTokens ++ s "(" :: argumentTokens ++ [s ")"]) (.call callee arguments)
    | trailing {calleeTokens callee bodyTokens body} : ExpressionSyntax .postfix calleeTokens callee →
        BlockExpressionSyntax bodyTokens body → ExpressionSyntax .postfix (calleeTokens ++ bodyTokens) (.call callee [body])
    | project {tokens subject field} : ExpressionSyntax .postfix tokens subject →
        ExpressionSyntax .postfix (tokens ++ [s ".",n field]) (.project subject field)
    | tupleProject {tokens subject token index} : ExpressionSyntax .postfix tokens subject → NaturalToken token index →
        ExpressionSyntax .postfix (tokens ++ [s ".",token]) (.project subject (toString index))
    | test {subjectTokens subject patternTokens pattern} : ExpressionSyntax .postfix subjectTokens subject →
        PatternSyntax patternTokens pattern → ExpressionSyntax .postfix (subjectTokens ++ w "is" :: patternTokens) (.test subject pattern)
    | postfix {tokens expression} : ExpressionSyntax .postfix tokens expression → ExpressionSyntax .prefixForm tokens expression
    | prefixForm {token operator tokens operand} : OperatorToken token operator → ExpressionSyntax .prefixForm tokens operand →
        ExpressionSyntax .prefixForm (token :: tokens) (.prefixForm operator operand)
    | borrow {tokens place} : ExpressionSyntax .prefixForm tokens place → ExpressionSyntax .prefixForm (s "&" :: tokens) (.borrow .shared place)
    | uniqueBorrow {tokens place} : ExpressionSyntax .prefixForm tokens place →
        ExpressionSyntax .prefixForm (s "&" :: w "mut" :: tokens) (.borrow .unique place)
    | dereference {tokens place} : ExpressionSyntax .prefixForm tokens place → ExpressionSyntax .prefixForm (s "*" :: tokens) (.dereference place)
    | move {tokens place} : ExpressionSyntax .prefixForm tokens place → ExpressionSyntax .prefixForm (w "move" :: tokens) (.move place)
    | unsafeAllowed {tokens body} : BlockExpressionSyntax tokens body → ExpressionSyntax .prefixForm (w "unsafe" :: tokens) (.unsafeBlock body)
    | tail {tokens callee arguments} : ExpressionSyntax .postfix tokens (.call callee arguments) →
        ExpressionSyntax .prefixForm (w "tail" :: tokens) (.tail callee arguments)
    | label {name annotationTokens annotation bodyTokens body} : OptionalTypeSyntax annotationTokens annotation →
        BlockExpressionSyntax bodyTokens body →
        ExpressionSyntax .prefixForm (.label name :: annotationTokens ++ bodyTokens) (.label name annotation body)
    | handle {computationTokens computation armTokens arms} : ExpressionSyntax .full computationTokens computation →
        HandlerArmsSyntax armTokens arms →
        ExpressionSyntax .prefixForm (w "handle" :: computationTokens ++ s "{" :: armTokens ++ [s "}"]) (.handle computation arms)
    | full {tokens expression} : ExpressionSyntax .prefixForm tokens expression → ExpressionSyntax .full tokens expression
    | operators {firstTokens first restTokens rest} : ExpressionSyntax .prefixForm firstTokens first → OperatorTailSyntax restTokens rest → rest ≠ [] →
        ExpressionSyntax .full (firstTokens ++ restTokens) (.operators first rest)

  inductive ExpressionsSyntax : Tokens → List Expr → Prop where
    | nil : ExpressionsSyntax [] []
    | one {tokens expression} : ExpressionSyntax .full tokens expression → ExpressionsSyntax tokens [expression]
    | cons {first rest expression expressions} : ExpressionSyntax .full first expression → ExpressionsSyntax rest expressions →
        ExpressionsSyntax (first ++ s "," :: rest) (expression :: expressions)

  inductive OperatorTailSyntax : Tokens → List (String × Expr) → Prop where
    | nil : OperatorTailSyntax [] []
    | cons {token operator first rest expression expressions} : OperatorToken token operator →
        ExpressionSyntax .prefixForm first expression → OperatorTailSyntax rest expressions →
        OperatorTailSyntax (token :: first ++ rest) ((operator,expression) :: expressions)

  inductive BlockSyntax : Tokens → List Statement → Option Expr → Prop where
    | emptyResult {tokens statements} : StatementsSyntax tokens statements → BlockSyntax (s "{" :: tokens ++ [s "}"]) statements none
    | result {statementTokens statements expressionTokens expression} : StatementsSyntax statementTokens statements →
        ExpressionSyntax .full expressionTokens expression →
        BlockSyntax (s "{" :: statementTokens ++ expressionTokens ++ [s "}"]) statements (some expression)

  inductive BlockExpressionSyntax : Tokens → Expr → Prop where
    | block {tokens statements result} : BlockSyntax tokens statements result → BlockExpressionSyntax tokens (.block statements result)
    | clauses {tokens arms} : arms ≠ [] → ArmsSyntax tokens arms → BlockExpressionSyntax (s "{" :: tokens ++ [s "}"]) (.clauses arms)
    | zero {tokens body} : ExpressionSyntax .full tokens body →
        BlockExpressionSyntax ([s "{",s "=>"] ++ tokens ++ [s "}"])
          (.function ⟨"",[],[],.infer,.row [] [],[],false,false⟩ body)

  inductive ArmsSyntax : Tokens → List (Pattern × Expr) → Prop where
    | one {patternTokens pattern bodyTokens body} : PatternSyntax patternTokens pattern → ExpressionSyntax .full bodyTokens body →
        ArmsSyntax (patternTokens ++ s "=>" :: bodyTokens) [(pattern,body)]
    | cons {patternTokens pattern bodyTokens body rest arms} : PatternSyntax patternTokens pattern →
        ExpressionSyntax .full bodyTokens body → ArmsSyntax rest arms →
        ArmsSyntax (patternTokens ++ s "=>" :: bodyTokens ++ s "," :: rest) ((pattern,body) :: arms)
    | trailing {tokens arms} : ArmsSyntax tokens arms → ArmsSyntax (tokens ++ [s ","]) arms

  inductive HandlerArmSyntax : Tokens → HandlerArm → Prop where
    | completion {patternTokens pattern bodyTokens body} : PatternSyntax patternTokens pattern → ExpressionSyntax .full bodyTokens body →
        HandlerArmSyntax (patternTokens ++ s "=>" :: bodyTokens) (.completion pattern body)
    | operation {pathTokens path argumentsTokens arguments patternTokens patterns bodyTokens body} : PathSyntax pathTokens path →
        ArgumentsSyntax argumentsTokens arguments → PatternsSyntax patternTokens patterns none → ExpressionSyntax .full bodyTokens body →
        HandlerArmSyntax (pathTokens ++ argumentsTokens ++ s "(" :: patternTokens ++ [s ")",s "=>"] ++ bodyTokens)
          (.operation path arguments patterns body)

  inductive HandlerArmsSyntax : Tokens → List HandlerArm → Prop where
    | nil : HandlerArmsSyntax [] []
    | one {tokens arm} : HandlerArmSyntax tokens arm → HandlerArmsSyntax tokens [arm]
    | cons {first rest arm arms} : HandlerArmSyntax first arm → HandlerArmsSyntax rest arms →
        HandlerArmsSyntax (first ++ s "," :: rest) (arm :: arms)

  inductive StatementSyntax : Tokens → Statement → Prop where
    | bind {patternTokens pattern annotationTokens annotation valueTokens value} : PatternSyntax patternTokens pattern →
        OptionalTypeSyntax annotationTokens annotation → ExpressionSyntax .full valueTokens value →
        StatementSyntax (w "let" :: patternTokens ++ annotationTokens ++ s "=" :: valueTokens ++ [s ";"])
          (.bind false pattern annotation value)
    | mutable {patternTokens pattern annotationTokens annotation valueTokens value} : PatternSyntax patternTokens pattern →
        OptionalTypeSyntax annotationTokens annotation → ExpressionSyntax .full valueTokens value →
        StatementSyntax ([w "let",w "mut"] ++ patternTokens ++ annotationTokens ++ s "=" :: valueTokens ++ [s ";"])
          (.bind true pattern annotation value)
    | assign {leftTokens left rightTokens right} : ExpressionSyntax .full leftTokens left → ExpressionSyntax .full rightTokens right →
        StatementSyntax (leftTokens ++ s "=" :: rightTokens ++ [s ";"]) (.assign left right)
    | discard {tokens expression} : ExpressionSyntax .full tokens expression → StatementSyntax (tokens ++ [s ";"]) (.discard expression)
    | item {tokens declaration} : DeclarationSyntax tokens declaration → StatementSyntax tokens (.item declaration)

  inductive StatementsSyntax : Tokens → List Statement → Prop where
    | nil : StatementsSyntax [] []
    | cons {first rest statement statements} : StatementSyntax first statement → StatementsSyntax rest statements →
        StatementsSyntax (first ++ rest) (statement :: statements)

  inductive DeclarationSyntax : Tokens → Declaration → Prop where
    | function {headTokens head bodyTokens body} : FunctionHeadSyntax headTokens head → head.name ≠ "" →
        BlockExpressionSyntax bodyTokens body → DeclarationSyntax (headTokens ++ bodyTokens) (.function head (some body))
    | signature {tokens head} : FunctionHeadSyntax tokens head → head.name ≠ "" →
        DeclarationSyntax (tokens ++ [s ";"]) (.function head none)
    | structure {name genericTokens generics whereTokens requirements fieldTokens fields} : GenericsSyntax genericTokens generics →
        WhereSyntax whereTokens requirements → FieldsSyntax fieldTokens fields → (∀ field ∈ fields, field.name.isSome = true) →
        DeclarationSyntax ([w "struct",n name] ++ genericTokens ++ whereTokens ++ s "{" :: fieldTokens ++ [s "}"])
          (.structure name generics fields true requirements)
    | tupleStructure {name genericTokens generics whereTokens requirements fieldTokens fields} : GenericsSyntax genericTokens generics →
        WhereSyntax whereTokens requirements → FieldsSyntax fieldTokens fields → (∀ field ∈ fields, field.name = none) →
        DeclarationSyntax ([w "struct",n name] ++ genericTokens ++ s "(" :: fieldTokens ++ [s ")"] ++ whereTokens ++ [s ";"])
          (.structure name generics fields false requirements)
    | unitStructure {name genericTokens generics whereTokens requirements} : GenericsSyntax genericTokens generics → WhereSyntax whereTokens requirements →
        DeclarationSyntax ([w "struct",n name] ++ genericTokens ++ whereTokens ++ [s ";"]) (.structure name generics [] false requirements)
    | enumeration {name genericTokens generics whereTokens requirements variantTokens variants} : GenericsSyntax genericTokens generics →
        WhereSyntax whereTokens requirements → VariantsSyntax variantTokens variants →
        DeclarationSyntax ([w "enum",n name] ++ genericTokens ++ whereTokens ++ s "{" :: variantTokens ++ [s "}"])
          (.enumeration name generics variants requirements)
    | trait {name genericTokens generics whereTokens requirements memberTokens members} : GenericsSyntax genericTokens generics →
        WhereSyntax whereTokens requirements → DeclarationsSyntax memberTokens members →
        DeclarationSyntax ([w "trait",n name] ++ genericTokens ++ whereTokens ++ s "{" :: memberTokens ++ [s "}"])
          (.trait name generics requirements members false)
    | unsafeTrait {tokens name generics requirements members} : DeclarationSyntax tokens (.trait name generics requirements members false) →
        DeclarationSyntax (w "unsafe" :: tokens) (.trait name generics requirements members true)
    | implementation {genericTokens generics traitTokens trait selfTokens self whereTokens requirements memberTokens members} :
        GenericsSyntax genericTokens generics → TypeSyntax traitTokens trait → TypeSyntax selfTokens self →
        WhereSyntax whereTokens requirements → DeclarationsSyntax memberTokens members →
        DeclarationSyntax (w "impl" :: genericTokens ++ traitTokens ++ n "for" :: selfTokens ++ whereTokens ++ s "{" :: memberTokens ++ [s "}"])
          (.implementation generics (some trait) self requirements members false false)
    | inherent {genericTokens generics selfTokens self whereTokens requirements memberTokens members} :
        GenericsSyntax genericTokens generics → TypeSyntax selfTokens self → WhereSyntax whereTokens requirements → DeclarationsSyntax memberTokens members →
        DeclarationSyntax (w "impl" :: genericTokens ++ selfTokens ++ whereTokens ++ s "{" :: memberTokens ++ [s "}"])
          (.implementation generics none self requirements members false false)
    | unsafeImpl {tokens generics trait self requirements members negative} :
        DeclarationSyntax tokens (.implementation generics trait self requirements members false negative) →
        DeclarationSyntax (w "unsafe" :: tokens) (.implementation generics trait self requirements members true negative)
    | negativeImpl {genericTokens generics traitTokens trait selfTokens self whereTokens requirements} : GenericsSyntax genericTokens generics →
        TypeSyntax traitTokens trait → TypeSyntax selfTokens self → WhereSyntax whereTokens requirements →
        DeclarationSyntax (w "impl" :: genericTokens ++ s "!" :: traitTokens ++ n "for" :: selfTokens ++ whereTokens ++ [s "{",s "}"])
          (.implementation generics (some trait) self requirements [] false true)
    | associated {name genericTokens generics whereTokens requirements} : GenericsSyntax genericTokens generics → WhereSyntax whereTokens requirements →
        DeclarationSyntax ([w "type",n name] ++ genericTokens ++ whereTokens ++ [s ";"]) (.associated name generics .type requirements none)
    | alias {name genericTokens generics valueTokens value} : GenericsSyntax genericTokens generics → TypeSyntax valueTokens value →
        DeclarationSyntax ([w "type",n name] ++ genericTokens ++ s "=" :: valueTokens ++ [s ";"]) (.alias name generics value)
    | effect {name genericTokens generics whereTokens requirements operationTokens operations} : GenericsSyntax genericTokens generics →
        WhereSyntax whereTokens requirements → OperationsSyntax operationTokens operations →
        DeclarationSyntax ([w "effect",n name] ++ genericTokens ++ whereTokens ++ s "{" :: operationTokens ++ [s "}"])
          (.effect name generics requirements operations)
    | constant {name genericTokens generics typeTokens type valueTokens value} : GenericsSyntax genericTokens generics →
        TypeSyntax typeTokens type → ExpressionSyntax .full valueTokens value →
        DeclarationSyntax ([w "const",n name] ++ genericTokens ++ s ":" :: typeTokens ++ s "=" :: valueTokens ++ [s ";"])
          (.constant name generics type value)
    | global {name typeTokens type valueTokens value} : TypeSyntax typeTokens type → ExpressionSyntax .full valueTokens value →
        DeclarationSyntax ([w "let",n name,s ":"] ++ typeTokens ++ s "=" :: valueTokens ++ [s ";"]) (.global name (some type) value)
    | module {name} : DeclarationSyntax [w "mod",n name,s ";"] (.module name none)
    | inlineModule {name tokens members} : DeclarationsSyntax tokens members →
        DeclarationSyntax ([w "mod",n name,s "{"] ++ tokens ++ [s "}"]) (.module name (some members))
    | import {tokens tree} : ImportSyntax tokens tree → DeclarationSyntax (w "use" :: tokens ++ [s ";"]) (.import tree)
    | fixity {kind word token precedence operatorToken operator targetTokens target} : NaturalToken token precedence →
        OperatorToken operatorToken operator →
        ((kind = .left ∧ word = "infixl") ∨ (kind = .right ∧ word = "infixr") ∨
          (kind = .nonassoc ∧ word = "infix") ∨ (kind = .prefixForm ∧ word = "prefix")) →
        ((target = none ∧ targetTokens = []) ∨ ∃ path tokens, target = some path ∧ targetTokens = s "=" :: tokens ∧ PathSyntax tokens path) →
        DeclarationSyntax ([w word,token,operatorToken] ++ targetTokens ++ [s ";"]) (.fixity kind precedence operator target)
    | foreign {tokens members} : DeclarationsSyntax tokens members →
        DeclarationSyntax ([w "extern",.literal (.string (text "C")),s "{"] ++ tokens ++ [s "}"]) (.foreign members false)
    | unsafeForeign {tokens members} : DeclarationSyntax tokens (.foreign members false) →
        DeclarationSyntax (w "unsafe" :: tokens) (.foreign members true)
    | visible {prefixTokens visibility tokens declaration} : VisibilitySyntax prefixTokens visibility → visibility ≠ .privateScope →
        DeclarationSyntax tokens declaration → DeclarationSyntax (prefixTokens ++ tokens) (.visible visibility declaration)
    | attributes {attributeTokens attributes tokens declaration} : AttributesSyntax attributeTokens attributes → attributes ≠ [] →
        DeclarationSyntax tokens declaration → DeclarationSyntax (attributeTokens ++ tokens) (.attributed attributes declaration)

  inductive DeclarationsSyntax : Tokens → List Declaration → Prop where
    | nil : DeclarationsSyntax [] []
    | cons {first rest declaration declarations} : DeclarationSyntax first declaration → DeclarationsSyntax rest declarations →
        DeclarationsSyntax (first ++ rest) (declaration :: declarations)
end

def ParsedAs (file : File) (declarations : List Declaration) : Prop :=
  ∃ tokens, Tokenizes file.id 0 file.bytes tokens ∧ DeclarationsSyntax (tokens.map LocatedToken.token) declarations

end Glorious.Language.Source
