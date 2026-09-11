import GloriousLanguage.Terms

/-! Source text and surface syntax (§§2–6, 10–14, 20). These are relations,
not a parser. Numeric magnitude selection belongs to elaboration, not lexing. -/
namespace Glorious.Language.Source

abbrev Text := List Nat
def text (s : String) : Text := s.toList.map Char.toNat
def UnicodeScalar (n : Nat) : Prop := n ≤ 0x10ffff ∧ ¬ (0xd800 ≤ n ∧ n ≤ 0xdfff)
def Initial (n : Nat) : Prop := n = 95 ∨ 65 ≤ n ∧ n ≤ 90 ∨ 97 ≤ n ∧ n ≤ 122
def Subsequent (n : Nat) : Prop := Initial n ∨ 48 ≤ n ∧ n ≤ 57
def Identifier (s : String) : Prop := ∃ first rest, text s = first :: rest ∧
  Initial first ∧ ∀ n ∈ rest, Subsequent n

def reserved : List String :=
  ["fn", "let", "mut", "const", "struct", "enum", "type", "trait", "impl", "where",
   "effect", "handle", "tail", "is", "move", "unsafe", "extern", "mod", "pub", "use",
   "infix", "infixl", "infixr", "prefix"]

/-- The byte representation is shortest-form, scalar-valid, and file-local. -/
inductive Encodes : Nat → List Nat → Prop where
  | ascii {n} : n < 0x80 → Encodes n [n]
  | two {a b} : 0xc2 ≤ a → a ≤ 0xdf → 0x80 ≤ b → b ≤ 0xbf →
      Encodes ((a - 0xc0) * 64 + b - 0x80) [a, b]
  | three {a b c n} : 0xe0 ≤ a → a ≤ 0xef →
      0x80 ≤ b → b ≤ 0xbf → 0x80 ≤ c → c ≤ 0xbf →
      n = (a - 0xe0) * 4096 + (b - 0x80) * 64 + c - 0x80 →
      0x800 ≤ n → UnicodeScalar n → Encodes n [a, b, c]
  | four {a b c d n} : 0xf0 ≤ a → a ≤ 0xf4 →
      0x80 ≤ b → b ≤ 0xbf → 0x80 ≤ c → c ≤ 0xbf → 0x80 ≤ d → d ≤ 0xbf →
      n = (a - 0xf0) * 262144 + (b - 0x80) * 4096 + (c - 0x80) * 64 + d - 0x80 →
      0x10000 ≤ n → UnicodeScalar n → Encodes n [a, b, c, d]

inductive Decodes : List Nat → Text → Prop where
  | nil : Decodes [] []
  | cons {bytes more scalar rest} : Encodes scalar bytes → Decodes more rest →
      Decodes (bytes ++ more) (scalar :: rest)

inductive Digit : Nat → Nat → Prop where
  | decimal {n} : n < 10 → Digit (48 + n) n
  | lower {n} : n < 6 → Digit (97 + n) (10 + n)
  | upper {n} : n < 6 → Digit (65 + n) (10 + n)

/-- Nonempty runs; underscores occur only between actual digits. -/
inductive Digits (base : Nat) : Text → List Nat → Prop where
  | one {c n} : Digit c n → n < base → Digits base [c] [n]
  | next {c n chars digits} : Digit c n → n < base → Digits base chars digits →
      Digits base (c :: chars) (n :: digits)
  | separator {c n chars digits} : Digit c n → n < base → Digits base chars digits →
      Digits base (c :: 95 :: chars) (n :: digits)

def digitsValue (base : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun total digit => total * base + digit) 0

structure IntegerLiteral where
  base : Nat
  digits : List Nat
  suffix : Option Scalar
  deriving Repr, Inhabited

structure FloatLiteral where
  whole : List Nat
  fractional : List Nat
  exponent : Int
  width : Option FloatWidth
  deriving Repr, Inhabited

inductive Literal where
  | integer (literal : IntegerLiteral)
  | floating (literal : FloatLiteral)
  | character (value : Nat)
  | byte (value : Nat)
  | string (scalars : Text)
  | bytes (octets : List Nat)
  deriving Repr, Inhabited

inductive Token where
  | name (value : String)
  | word (value : String)
  | symbol (value : String)
  | lifetime (value : String)
  | label (value : String)
  | literal (value : Literal)
  deriving Repr, Inhabited

inductive Escape : Text → Nat → Prop where
  | newline : Escape (text "\\n") 10
  | carriage : Escape (text "\\r") 13
  | tab : Escape (text "\\t") 9
  | zero : Escape (text "\\0") 0
  | slash : Escape (text "\\\\") 92
  | quote : Escape (text "\\\"") 34
  | apostrophe : Escape (text "\\'") 39
  | ascii {a b x y} : Digit a x → Digit b y → 16*x+y < 128 →
      Escape ([92, 120, a, b]) (16*x+y)
  | unicode {chars digits n} : Digits 16 chars digits → ¬ 95 ∈ chars →
      n = digitsValue 16 digits → UnicodeScalar n → Escape (text "\\u{" ++ chars ++ [125]) n

inductive Quoted (delimiter : Nat) : Text → Text → Prop where
  | nil : Quoted delimiter [] []
  | plain {c rest values} : UnicodeScalar c → c ≠ delimiter → c ≠ 92 → c ≠ 10 → c ≠ 13 →
      Quoted delimiter rest values → Quoted delimiter (c :: rest) (c :: values)
  | escape {chars c rest values} : Escape chars c → Quoted delimiter rest values →
      Quoted delimiter (chars ++ rest) (c :: values)

inductive ByteQuoted (delimiter : Nat) : Text → List Nat → Prop where
  | nil : ByteQuoted delimiter [] []
  | plain {c rest values} : c < 128 → c ≠ delimiter → c ≠ 92 → c ≠ 10 → c ≠ 13 →
      ByteQuoted delimiter rest values → ByteQuoted delimiter (c :: rest) (c :: values)
  | basic {chars c rest values} : Escape chars c → c < 128 →
      ByteQuoted delimiter rest values → ByteQuoted delimiter (chars ++ rest) (c :: values)
  | byte {a b x y rest values} : Digit a x → Digit b y → x < 16 → y < 16 →
      ByteQuoted delimiter rest values → ByteQuoted delimiter ([92,120,a,b] ++ rest) (16*x+y :: values)

inductive IntegerSuffix : Option Scalar → Text → Prop where
  | absent : IntegerSuffix none []
  | unsigned {bits} : bits ∈ [8,16,32,64,128] →
      IntegerSuffix (some (.integer false (.fixed bits))) (text ("u" ++ toString bits))
  | signed {bits} : bits ∈ [8,16,32,64,128] →
      IntegerSuffix (some (.integer true (.fixed bits))) (text ("i" ++ toString bits))
  | usize : IntegerSuffix (some (.integer false .pointer)) (text "usize")
  | isize : IntegerSuffix (some (.integer true .pointer)) (text "isize")

inductive FloatSuffix : Option FloatWidth → Text → Prop where
  | absent : FloatSuffix none []
  | single : FloatSuffix (some .single) (text "f32")
  | double : FloatSuffix (some .double) (text "f64")

inductive Exponent : Text → Int → Prop where
  | absent : Exponent [] 0
  | positive {e chars digits} : e = 101 ∨ e = 69 → Digits 10 chars digits →
      Exponent (e :: chars) (Int.ofNat (digitsValue 10 digits))
  | plus {e chars digits} : e = 101 ∨ e = 69 → Digits 10 chars digits →
      Exponent (e :: 43 :: chars) (Int.ofNat (digitsValue 10 digits))
  | negative {e chars digits} : e = 101 ∨ e = 69 → Digits 10 chars digits →
      Exponent (e :: 45 :: chars) (-Int.ofNat (digitsValue 10 digits))

inductive SpellsToken : Token → Text → Prop where
  | name {s} : Identifier s → s ∉ reserved → SpellsToken (.name s) (text s)
  | word {s} : s ∈ reserved → SpellsToken (.word s) (text s)
  | lifetime {s} : Identifier s → SpellsToken (.lifetime s) (39 :: text s)
  | label {s} : Identifier s → SpellsToken (.label s) (64 :: text s)
  | symbol {s} : s ∈ ["(",")","[","]","{","}",",",";",":","::",".","..","<",">",
      "=","->","=>","&","*","/","|","!","+","-","%","==","!=","<=",">=","#"] →
      SpellsToken (.symbol s) (text s)
  | operator {s} : text s ≠ [] →
      (∀ c ∈ text s, c ∈ text "+-%!<>=^~?") →
      s ∉ ["=","->","=>","<",">","!","+","-","%","==","!=","<=",">="] →
      SpellsToken (.symbol s) (text s)
  | integer {base prefix chars digits suffix suffixChars} :
      (base = 10 ∧ prefix = [] ∨ base = 2 ∧ prefix = text "0b" ∨
       base = 8 ∧ prefix = text "0o" ∨ base = 16 ∧ prefix = text "0x") →
      Digits base chars digits → IntegerSuffix suffix suffixChars →
      SpellsToken (.literal (.integer ⟨base,digits,suffix⟩)) (prefix ++ chars ++ suffixChars)
  | float {wholeChars whole fractionChars fraction exponentChars exponent suffixChars suffix} :
      Digits 10 wholeChars whole →
      (fractionChars = [] ∧ fraction = [] ∨ ∃ chars, Digits 10 chars fraction ∧ fractionChars = 46 :: chars) →
      Exponent exponentChars exponent → FloatSuffix suffix suffixChars →
      (fractionChars ≠ [] ∨ exponentChars ≠ [] ∨ suffixChars ≠ []) →
      SpellsToken (.literal (.floating ⟨whole,fraction,exponent,suffix⟩))
        (wholeChars ++ fractionChars ++ exponentChars ++ suffixChars)
  | character {chars value} : Quoted 39 chars [value] →
      SpellsToken (.literal (.character value)) ([39] ++ chars ++ [39])
  | byte {chars value} : ByteQuoted 39 chars [value] →
      SpellsToken (.literal (.byte value)) ([98,39] ++ chars ++ [39])
  | string {chars values} : Quoted 34 chars values →
      SpellsToken (.literal (.string values)) ([34] ++ chars ++ [34])
  | bytes {chars values} : ByteQuoted 34 chars values →
      SpellsToken (.literal (.bytes values)) ([98,34] ++ chars ++ [34])

inductive CommentBody : Text → Prop where
  | nil : CommentBody []
  | ordinary {c rest} : c ≠ 42 → c ≠ 47 → CommentBody rest → CommentBody (c :: rest)
  | slashLast : CommentBody [47]
  | starLast : CommentBody [42]
  | slash {c rest} : c ≠ 42 → CommentBody (c :: rest) → CommentBody (47 :: c :: rest)
  | star {c rest} : c ≠ 47 → CommentBody (c :: rest) → CommentBody (42 :: c :: rest)
  | nested {inside rest} : CommentBody inside → CommentBody rest →
      CommentBody (text "/*" ++ inside ++ text "*/" ++ rest)

inductive Trivia : Text → Prop where
  | nil : Trivia []
  | space {c rest} : c ∈ [9,10,13,32] → Trivia rest → Trivia (c :: rest)
  | block {inside rest} : CommentBody inside → Trivia rest →
      Trivia (text "/*" ++ inside ++ text "*/" ++ rest)
  | line {inside rest} : 10 ∉ inside → 13 ∉ inside → Trivia rest →
      Trivia (text "//" ++ inside ++ [10] ++ rest)
  | crlf {inside rest} : 10 ∉ inside → 13 ∉ inside → Trivia rest →
      Trivia (text "//" ++ inside ++ [13,10] ++ rest)

structure LocatedToken where
  token : Token
  span : Span
  deriving Repr, Inhabited

inductive Tokenizes (file : Identity) : Nat → List Nat → List LocatedToken → Prop where
  | end {offset bytes chars} : Decodes bytes chars → Trivia chars → Tokenizes file offset bytes []
  | finalComment {offset prefixBytes commentBytes prefixChars commentChars} :
      Decodes prefixBytes prefixChars → Trivia prefixChars → Decodes commentBytes commentChars →
      10 ∉ commentChars → 13 ∉ commentChars →
      Tokenizes file offset (prefixBytes ++ [47,47] ++ commentBytes) []
  | token {offset triviaBytes triviaChars bytes chars remaining token tokens} :
      Decodes triviaBytes triviaChars → Trivia triviaChars → Decodes bytes chars → SpellsToken token chars →
      bytes ≠ [] →
      (∀ more later other text', remaining = more ++ later →
        Decodes (bytes ++ more) text' → SpellsToken other text' → more = []) →
      Tokenizes file (offset + triviaBytes.length + bytes.length) remaining tokens →
      Tokenizes file offset (triviaBytes ++ bytes ++ remaining)
        (⟨token,⟨file,offset + triviaBytes.length,offset + triviaBytes.length + bytes.length⟩⟩ :: tokens)
  | bom {bytes tokens} : Tokenizes file 3 bytes tokens → Tokenizes file 0 ([0xef,0xbb,0xbf] ++ bytes) tokens

abbrev Path := List String

inductive TypeExpr where
  | path (name : Path) (ownerArguments itemArguments : List TypeExpr)
  | infer | unit | bottom
  | tuple (fields : List TypeExpr)
  | array (element length : TypeExpr)
  | reference (mode : Mutability) (region : Option String) (referent : TypeExpr)
  | pointer (mode : Mutability) (referent : TypeExpr)
  | lifetime (name : String)
  | constant (literal : Literal)
  | quantity (value : Quantity)
  | binding (name : String) (value : TypeExpr)
  | constructor (path : Path) (arguments fields : List TypeExpr)
  | row (instances tails : List TypeExpr)
  | associated (owner : TypeExpr) (trait : Path) (traitArguments : List TypeExpr)
      (member : String) (arguments : List TypeExpr)
  deriving Repr, Inhabited

inductive Pattern where
  | wildcard | binder (name : String) (explicit : Bool)
  | constant (path : Path) (arguments : List TypeExpr)
  | literal (value : Literal)
  | tuple (fields : List Pattern) (remainder : Option Nat)
  | array (fields : List Pattern) (remainder : Option Nat)
  | constructor (path : Path) (arguments : List TypeExpr) (fields : List Pattern) (remainder : Option Nat)
  | record (path : Path) (arguments : List TypeExpr) (fields : List (String × Pattern)) (remainder : Bool)
  | reference (mode : Mutability) (pattern : Pattern)
  deriving Repr, Inhabited

inductive Predicate where
  | equal (a b : TypeExpr)
  | outlives (a b : TypeExpr)
  | bound (subject : TypeExpr) (trait : Path) (arguments : List TypeExpr) (unsafe : Bool) (negative : Bool)
  | quantified (binders : List (String × Kind)) (requirements : List Predicate)
  deriving Repr, Inhabited

structure Generic where
  name : String
  kind : Kind
  defaultValue : Option TypeExpr := none
  constantType : Option TypeExpr := none
  deriving Repr, Inhabited

structure Parameter where
  pattern : Pattern
  type : TypeExpr
  deriving Repr, Inhabited

structure FunctionHead where
  name : String
  generics : List Generic := []
  parameters : List Parameter
  result : TypeExpr := .unit
  effects : TypeExpr := .row [] []
  requirements : List Predicate := []
  unsafe : Bool := false
  cABI : Bool := false
  deriving Repr, Inhabited

structure Field where
  name : Option String
  type : TypeExpr
  visibility : Visibility := .private
  deriving Repr, Inhabited

structure Variant where
  name : String
  fields : List Field
  record : Bool
  deriving Repr, Inhabited

structure Operation where
  name : String
  generics : List Generic := []
  payload : List TypeExpr
  result : TypeExpr := .unit
  quantity : Option Quantity := none
  requirements : List Predicate := []
  deriving Repr, Inhabited

inductive ImportTree where
  | name (path : Path) (rename : Option String)
  | glob (path : Path)
  | group (path : Path) (children : List ImportTree)
  deriving Repr, Inhabited

inductive FixityKind where
  | left | right | nonassoc | prefix
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Attribute where
  | reprC | transparent | reprInteger (signed : Bool) (width : Width)
  | nonExhaustive | exportName (name : String)
  | noStd | noPrelude | metadata (identity : DeclId) (payload : Text)
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | literal (value : Literal)
    | name (path : Path) (ownerArguments itemArguments : List TypeExpr)
    | labelName (name : String)
    | unit | tuple (fields : List Expr) | array (fields : List Expr)
    | call (callee : Expr) (arguments : List Expr)
    | block (statements : List Statement) (result : Option Expr)
    | function (head : FunctionHead) (body : Expr)
    | clauses (arms : List (Pattern × Expr))
    | capture (places : List Expr) (body : Expr)
    | project (subject : Expr) (field : String)
    | borrow (mode : Mutability) (place : Expr)
    | dereference (place : Expr)
    | move (place : Expr)
    | test (subject : Expr) (pattern : Pattern)
    | handle (computation : Expr) (arms : List HandlerArm)
    | label (name : String) (annotation : Option TypeExpr) (body : Expr)
    | tail (callee : Expr) (arguments : List Expr)
    | unsafeBlock (body : Expr)
    | operators (first : Expr) (rest : List (String × Expr))
    | prefix (operator : String) (operand : Expr)
    deriving Repr, Inhabited

  inductive Statement where
    | bind (mutable : Bool) (pattern : Pattern) (annotation : Option TypeExpr) (value : Expr)
    | assign (destination value : Expr)
    | discard (value : Expr)
    | item (declaration : Declaration)
    deriving Repr, Inhabited

  inductive HandlerArm where
    | completion (pattern : Pattern) (body : Expr)
    | operation (path : Path) (arguments : List TypeExpr) (patterns : List Pattern) (body : Expr)
    deriving Repr, Inhabited

  inductive Declaration where
    | function (head : FunctionHead) (body : Option Expr)
    | structure (name : String) (generics : List Generic) (fields : List Field) (record : Bool)
        (requirements : List Predicate)
    | enumeration (name : String) (generics : List Generic) (variants : List Variant)
        (requirements : List Predicate)
    | trait (name : String) (generics : List Generic) (requirements : List Predicate)
        (members : List Declaration) (unsafe : Bool)
    | implementation (generics : List Generic) (trait : Option TypeExpr) (self : TypeExpr)
        (requirements : List Predicate) (members : List Declaration) (unsafe negative : Bool)
    | associated (name : String) (generics : List Generic) (kind : Kind)
        (requirements : List Predicate) (value : Option TypeExpr)
    | effect (name : String) (generics : List Generic) (requirements : List Predicate)
        (operations : List Operation)
    | alias (name : String) (generics : List Generic) (value : TypeExpr)
    | constant (name : String) (generics : List Generic) (type : TypeExpr) (value : Expr)
    | global (name : String) (type : Option TypeExpr) (value : Expr)
    | module (name : String) (inline : Option (List Declaration))
    | import (tree : ImportTree)
    | fixity (kind : FixityKind) (precedence : Nat) (operator : String) (target : Option Path)
    | foreign (members : List Declaration) (unsafe : Bool)
    | visible (visibility : Visibility) (declaration : Declaration)
    | attributed (attributes : List Attribute) (declaration : Declaration)
    deriving Repr, Inhabited
end

structure File where
  id : Identity
  package : Identity
  logicalPath : List String
  bytes : List Nat
  deriving Repr, Inhabited

theorem ordinary_control_names :
    "if" ∉ reserved ∧ "loop" ∉ reserved ∧ "return" ∉ reserved ∧ "true" ∉ reserved := by decide

theorem no_surrogate {n bytes} (encoded : Encodes n bytes) : UnicodeScalar n := by
  cases encoded <;> simp_all [UnicodeScalar] <;> omega

end Glorious.Language.Source
