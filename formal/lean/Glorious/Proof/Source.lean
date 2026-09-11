import Glorious.Semantics.Manifest
import Glorious.Proof.Elaboration

/-! Source identity and grammar judgments. None of the rules calls the lexer
or parser to decide what the source means. Spans refer to the original bytes,
and source-closure completeness is a separate obligation from parsing a file. -/
namespace Glorious.Semantics.Spec.Source

def Scalar (value : Nat) : Prop := value ≤ 0x10ffff ∧ ¬ (0xd800 ≤ value ∧ value ≤ 0xdfff)

inductive UTF8 : List UInt8 → Nat → Prop where
  | ascii {a} (bound : a < 128) : UTF8 [UInt8.ofNat a] a
  | two {a b} (lead : 0xc2 ≤ a ∧ a ≤ 0xdf) (tail : 0x80 ≤ b ∧ b ≤ 0xbf) :
      UTF8 [UInt8.ofNat a, UInt8.ofNat b] ((a - 0xc0) * 64 + b - 0x80)
  | three {a b c value}
      (lead : 0xe0 ≤ a ∧ a ≤ 0xef) (second : 0x80 ≤ b ∧ b ≤ 0xbf) (third : 0x80 ≤ c ∧ c ≤ 0xbf)
      (decoded : value = (a - 0xe0) * 4096 + (b - 0x80) * 64 + c - 0x80)
      (shortest : 0x800 ≤ value) (valid : Scalar value) :
      UTF8 [UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c] value
  | four {a b c d value}
      (lead : 0xf0 ≤ a ∧ a ≤ 0xf4)
      (second : 0x80 ≤ b ∧ b ≤ 0xbf) (third : 0x80 ≤ c ∧ c ≤ 0xbf) (fourth : 0x80 ≤ d ∧ d ≤ 0xbf)
      (decoded : value = (a - 0xf0) * 262144 + (b - 0x80) * 4096 + (c - 0x80) * 64 + d - 0x80)
      (shortest : 0x10000 ≤ value) (valid : Scalar value) :
      UTF8 [UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c, UInt8.ofNat d] value

inductive Decodes : Nat → List UInt8 → List SourceCharacter → Prop where
  | nil {offset} : Decodes offset [] []
  | cons {offset bytes rest scalar characters}
      (head : UTF8 bytes scalar) (tail : Decodes (offset + bytes.length) rest characters) :
      Decodes offset (bytes ++ rest) (⟨scalar, offset, bytes.length⟩ :: characters)

def Decoded (file : SourceFile) (characters : Array SourceCharacter) : Prop :=
  Decodes 0 file.bytes.data.toList characters.toList ∨
  ∃ rest, file.bytes.data.toList = [0xef, 0xbb, 0xbf] ++ rest ∧ Decodes 3 rest characters.toList

def Letter (scalar : Nat) : Prop := 65 ≤ scalar ∧ scalar ≤ 90 ∨ 97 ≤ scalar ∧ scalar ≤ 122 ∨ scalar = 95
def Digit (scalar : Nat) : Prop := 48 ≤ scalar ∧ scalar ≤ 57
def Identifier (scalars : List Nat) (name : String) : Prop :=
  (∃ first rest, scalars = first :: rest ∧ Letter first ∧ ∀ scalar ∈ rest, Letter scalar ∨ Digit scalar) ∧
  name = String.ofList (scalars.map Char.ofNat)

inductive Escape : List Nat → Nat → Prop where
  | newline : Escape [92, 110] 10
  | return_ : Escape [92, 114] 13
  | tab : Escape [92, 116] 9
  | zero : Escape [92, 48] 0
  | literal {value} (allowed : value = 92 ∨ value = 39 ∨ value = 34) : Escape [92, value] value
  | hex {a b x y} (first : hexDigit a = some x) (second : hexDigit b = some y) : Escape [92, 120, a, b] (x * 16 + y)

inductive Quoted (quote : Nat) (byte : Bool) : List Nat → List Nat → Prop where
  | nil : Quoted quote byte [] []
  | plain {head tail decoded} (notQuote : head ≠ quote) (notEscape : head ≠ 92)
      (valid : Scalar head) (ascii : byte = true → head < 128)
      (rest : Quoted quote byte tail decoded) : Quoted quote byte (head :: tail) (head :: decoded)
  | escape {spelling scalar rest decoded}
      (escaped : Escape spelling scalar) (valid : Scalar scalar)
      (range : byte = true → scalar < 256)
      (tail : Quoted quote byte rest decoded) : Quoted quote byte (spelling ++ rest) (scalar :: decoded)

inductive BalancedComment : List Nat → Prop where
  | empty : BalancedComment []
  | character {scalar rest} (notDelimiter : scalar ≠ 42 ∧ scalar ≠ 47)
      (tail : BalancedComment rest) : BalancedComment (scalar :: rest)
  | star {rest} (notClosing : ∀ tail, rest ≠ 47 :: tail) (tail : BalancedComment rest) :
      BalancedComment (42 :: rest)
  | slash {rest} (notOpening : ∀ tail, rest ≠ 42 :: tail) (tail : BalancedComment rest) :
      BalancedComment (47 :: rest)
  | nested {inside rest} (body : BalancedComment inside) (tail : BalancedComment rest) :
      BalancedComment ([47, 42] ++ inside ++ [42, 47] ++ rest)

inductive Trivia : List Nat → Prop where
  | empty : Trivia []
  | whitespace {scalar rest} (space : scalar = 32 ∨ scalar = 9 ∨ scalar = 10 ∨ scalar = 13)
      (tail : Trivia rest) : Trivia (scalar :: rest)
  | line {characters newline rest} (content : ∀ scalar ∈ characters, scalar ≠ 10 ∧ scalar ≠ 13)
      (terminator : newline = 10 ∨ newline = 13)
      (tail : Trivia rest) : Trivia ([47, 47] ++ characters ++ newline :: rest)
  | block {characters rest} (nested : BalancedComment characters) (tail : Trivia rest) :
      Trivia ([47, 42] ++ characters ++ [42, 47] ++ rest)

def FinalTrivia (characters : List Nat) : Prop :=
  Trivia characters ∨ ∃ leading comment, characters = leading ++ [47, 47] ++ comment ∧
    Trivia leading ∧ ∀ scalar ∈ comment, scalar ≠ 10 ∧ scalar ≠ 13

inductive TokenText : List Nat → TokenKind → Prop where
  | identifier {scalars name} : Identifier scalars name → TokenText scalars (.identifier name)
  | lifetime {scalars name} : Identifier scalars name → TokenText (39 :: scalars) (.lifetime name)
  | label {scalars name} : Identifier scalars name → TokenText (64 :: scalars) (.label name)
  | punctuation {name}
      (permitted : name ∈ ["(", ")", "[", "]", "{", "}", ",", ";", ":", "::", ".", "..", "=", "=>", "->", "&", "!", "<", ">", "+", "-", "*", "/", "%", "|", "^", "~", "?", "==", "!=", "<=", ">="] ) :
      TokenText (name.toList.map Char.toNat) (.punctuation name)
  | string {spelling values byte}
      (quoted : Quoted 34 byte spelling values) :
      TokenText ((if byte then [98, 34] else [34]) ++ spelling ++ [34])
        (.string (if byte then values.map UInt8.ofNat else values.flatMap encodeScalar) byte)
  | character {spelling scalar byte}
      (quoted : Quoted 39 byte spelling [scalar]) :
      TokenText ((if byte then [98, 39] else [39]) ++ spelling ++ [39]) (.character scalar byte)
  | number {first rest}
      (starts : Digit first)
      (continues : ∀ scalar ∈ rest, Letter scalar ∨ Digit scalar ∨ scalar = 46 ∨ scalar = 43 ∨ scalar = 45) :
      TokenText (first :: rest) (.number (String.ofList ((first :: rest).map Char.ofNat)))

inductive Tokenizes (file : Id) : List SourceCharacter → List Token → Prop where
  | end_ {characters offset} (trivia : FinalTrivia (characters.map (·.scalar))) :
      Tokenizes file characters [⟨.eof, ⟨file, offset, offset⟩⟩]
  | token {before characters rest kind tokens first last}
      (trivia : Trivia (before.map (·.scalar)))
      (text : TokenText (characters.map (·.scalar)) kind)
      (nonempty : characters ≠ [])
      (start : characters.head? = some first)
      (stop : characters.getLast? = some last)
      (maximal : ∀ extra remaining longer,
        rest = extra ++ remaining → extra ≠ [] →
        ¬ TokenText ((characters ++ extra).map (·.scalar)) longer)
      (tail : Tokenizes file rest tokens) :
      Tokenizes file (before ++ characters ++ rest)
        (⟨kind, ⟨file, first.offset, last.offset + last.width⟩⟩ :: tokens)

def Lexed (file : SourceFile) (tokens : Array Token) : Prop :=
  ∃ characters, Decoded file characters ∧ Tokenizes file.identity characters.toList tokens.toList ∧
    tokens.toList.getLast? = some ⟨.eof, ⟨file.identity, file.bytes.size, file.bytes.size⟩⟩

def Says (token : Token) (spelling : String) : Prop :=
  token.kind = .identifier spelling ∨ token.kind = .punctuation spelling

inductive Separated (element : List Token → α → Prop) : List Token → List α → Prop where
  | nil : Separated element [] []
  | one {tokens value} (item : element tokens value) : Separated element tokens [value]
  | trailing {tokens value comma} (item : element tokens value) (delimiter : Says comma ",") :
      Separated element (tokens ++ [comma]) [value]
  | cons {tokens value comma rest values} (item : element tokens value) (delimiter : Says comma ",")
      (tail : Separated element rest values) : Separated element (tokens ++ comma :: rest) (value :: values)

inductive TypeSyntax : List Token → Term → Prop where
  | unit {left right} (open_ : Says left "(") (close : Says right ")") : TypeSyntax [left, right] .unit
  | bottom {token} (spelling : Says token "!") : TypeSyntax [token] .bottom
  | scalar {token spelling type} (name : token.kind = .identifier spelling)
      (builtin : parseScalarType spelling = some type) : TypeSyntax [token] (.scalar type)
  | tuple {left body right types} (open_ : Says left "(") (close : Says right ")")
      (fields : Separated TypeSyntax body types) : TypeSyntax (left :: body ++ [right]) (.tuple types)
  | reference {amp lifetime mutToken body mode name type}
      (open_ : Says amp "&") (region : lifetime.kind = .lifetime name)
      (modeSyntax : (mode = .shared ∧ mutToken = []) ∨
        (mode = .unique ∧ ∃ token, mutToken = [token] ∧ Says token "mut"))
      (referent : TypeSyntax body type) :
      TypeSyntax (amp :: lifetime :: mutToken ++ body) (.reference mode (.named [name] [] .region) type)

mutual
  inductive ExpressionSyntax : List Token → Expr → Prop where
    | unit {left right} (open_ : Says left "(") (close : Says right ")") :
        ExpressionSyntax [left, right] (.unit left.span)
    | name {token name} (identifier : token.kind = .identifier name) :
        ExpressionSyntax [token] (.name token.span ⟨[name]⟩ [])
    | character {token scalar} (literal : token.kind = .character scalar false) :
        ExpressionSyntax [token] (.literal token.span (.character scalar))
    | text {token bytes} (literal : token.kind = .string bytes false) :
        ExpressionSyntax [token] (.literal token.span (.text bytes))
    | bytes {token bytes} (literal : token.kind = .string bytes true) :
        ExpressionSyntax [token] (.literal token.span (.bytes bytes))
    | tuple {left body right values}
        (open_ : Says left "(") (close : Says right ")") (fields : Separated ExpressionSyntax body values) :
        ExpressionSyntax (left :: body ++ [right]) (.tuple left.span values)
    | array {left body right values}
        (open_ : Says left "[") (close : Says right "]") (fields : Separated ExpressionSyntax body values) :
        ExpressionSyntax (left :: body ++ [right]) (.array left.span values)
    | apply {receiverTokens receiver left argumentsTokens arguments right}
        (callee : ExpressionSyntax receiverTokens receiver)
        (open_ : Says left "(") (close : Says right ")")
        (inputs : Separated ExpressionSyntax argumentsTokens arguments) :
        ExpressionSyntax (receiverTokens ++ left :: argumentsTokens ++ [right]) (.apply receiver.span receiver arguments)
    | borrow {token body value} (keyword : Says token "&") (referent : ExpressionSyntax body value) :
        ExpressionSyntax (token :: body) (.borrow token.span .shared value)
    | borrowUnique {token mutToken body value} (keyword : Says token "&") (mutableKeyword : Says mutToken "mut")
        (referent : ExpressionSyntax body value) : ExpressionSyntax (token :: mutToken :: body) (.borrow token.span .unique value)
    | move {token body value} (keyword : Says token "move") (referent : ExpressionSyntax body value) :
        ExpressionSyntax (token :: body) (.move token.span value)
    | unsafeScope {token body value} (keyword : Says token "unsafe") (bodyProof : ExpressionSyntax body value) :
        ExpressionSyntax (token :: body) (.unsafeScope token.span value)
    | block {left tokens right statements result}
        (open_ : Says left "{") (close : Says right "}") (body : BlockSyntax tokens statements result) :
        ExpressionSyntax (left :: tokens ++ [right]) (.block left.span statements result)
  inductive BlockSyntax : List Token → List Statement → Option Expr → Prop where
    | empty : BlockSyntax [] [] none
    | result {tokens expression} (body : ExpressionSyntax tokens expression) : BlockSyntax tokens [] (some expression)
    | discard {tokens expression semicolon rest statements result}
        (body : ExpressionSyntax tokens expression) (end_ : Says semicolon ";") (tail : BlockSyntax rest statements result) :
        BlockSyntax (tokens ++ semicolon :: rest) (.discard expression.span expression :: statements) result
    | assign {left destination equal right value semicolon rest statements result}
        (destinationProof : ExpressionSyntax left destination) (assignment : Says equal "=")
        (valueProof : ExpressionSyntax right value) (end_ : Says semicolon ";")
        (tail : BlockSyntax rest statements result) :
        BlockSyntax (left ++ equal :: right ++ semicolon :: rest) (.assign equal.span destination value :: statements) result
end

inductive FunctionSyntax (module : ModuleId) : List Token → FunctionDecl → Prop where
  | function {keyword name left parameters right arrow outputTokens bodyTokens nameText output function body}
      (fn : Says keyword "fn") (identifier : name.kind = .identifier nameText)
      (open_ : Says left "(") (close : Says right ")")
      (parameterSyntax : parameters = [] ∧ function.parameters = [])
      (resultSyntax : (arrow = [] ∧ outputTokens = [] ∧ output = .unit) ∨
        (∃ token, arrow = [token] ∧ Says token "->" ∧ TypeSyntax outputTokens output))
      (bodyProof : ExpressionSyntax bodyTokens body)
      (header : function.header.module = module ∧ function.header.name = nameText ∧ function.header.span = name.span)
      (signature : function.signature.arguments = [] ∧ function.signature.output = output ∧
        function.signature.generics = [] ∧ function.signature.effects = .row [] [] ∧
        function.signature.unsafeCall = false ∧ function.signature.abi = .glorious)
      (value : function.body = some body ∧ function.runtimeBinding = none) :
      FunctionSyntax module ([keyword, name, left] ++ parameters ++ [right] ++ arrow ++ outputTokens ++ bodyTokens) function

inductive ItemsSyntax (module : ModuleId) : List Token → List FunctionDecl → Prop where
  | empty {eof} (end_ : eof.kind = .eof) : ItemsSyntax module [eof] []
  | function {tokens function rest functions} (head : FunctionSyntax module tokens function)
      (tail : ItemsSyntax module rest functions) : ItemsSyntax module (tokens ++ rest) (function :: functions)

structure ParsedFile (file : SourceFile) (before after : Program) : Prop where
  derivation : ∃ tokens declarations, Lexed file tokens ∧ ItemsSyntax file.module tokens.toList declarations ∧
    after.functions = before.functions ++ declarations
  identity : after.packages = before.packages ∧ after.target = before.target ∧
    after.dataTypes = before.dataTypes ∧ after.traits = before.traits ∧ after.effects = before.effects ∧
    after.implementations = before.implementations ∧ after.aliases = before.aliases ∧
    after.constants = before.constants ∧ after.fixities = before.fixities
  unique : (after.functions.map (·.header.id)).Nodup

inductive ParsedFiles : Program → List SourceFile → Program → Prop where
  | nil {program} : ParsedFiles program [] program
  | cons {before middle after file files}
      (head : ParsedFile file before middle) (tail : ParsedFiles middle files after) :
      ParsedFiles before (file :: files) after

theorem ParsedFiles.append (first : ParsedFiles initial earlier middle)
    (second : ParsedFiles middle suffix final) : ParsedFiles initial (earlier ++ suffix) final := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head (ih second)

structure ClosedSources (initial : Program) (files : List SourceFile) (program : Program) : Prop where
  parsed : ParsedFiles initial files program
  identities : (files.map (·.identity)).Nodup
  modules : (files.map (·.module)).Nodup
  roots : ∀ package ∈ program.packages, ∃ file ∈ files, file.module = package.root
  children : ∀ parent ∈ program.modules, ∀ child ∈ parent.children,
    ∃ file ∈ files, file.module = child
  declared : ∀ file ∈ files, (∃ package ∈ program.packages, package.root = file.module) ∨
    ∃ parent ∈ program.modules, file.module ∈ parent.children

end Glorious.Semantics.Spec.Source
