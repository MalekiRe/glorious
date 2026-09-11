import Glorious.Semantics.Model

namespace Glorious.Semantics

structure SourceFile where
  identity : Id
  module : ModuleId
  path : String
  bytes : ByteArray

instance : Repr SourceFile where
  reprPrec file _ := repr (file.identity, file.module, file.path, file.bytes.data)

structure SourceCharacter where
  scalar : Nat
  offset : Nat
  width : Nat
  deriving Repr

def asciiLetter (n : Nat) : Bool := (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 95
def asciiDigit (n : Nat) : Bool := 48 ≤ n && n ≤ 57
def identifierContinue (n : Nat) : Bool := asciiLetter n || asciiDigit n
def hexDigit (n : Nat) : Option Nat :=
  if asciiDigit n then some (n - 48) else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else if 97 ≤ n && n ≤ 102 then some (n - 87) else none

/-- Validate every source byte, including comments, with shortest-form UTF-8.
    Offsets always refer to the supplied file, never to a replacement string. -/
def decodeSource (file : SourceFile) : Check (Array SourceCharacter) := do
  let bytes := file.bytes.data
  let rec decode : Nat → Nat → Array SourceCharacter → Check (Array SourceCharacter)
    | 0, offset, output =>
      if offset == bytes.size then return output else reject .resourceLimit "source decoder budget exhausted"
    | fuel + 1, offset, output => do
      if offset == bytes.size then return output
      let first := (bytes[offset]!).toNat
      let (width, initial, minimum) := if first < 0x80 then (1, first, 0)
        else if 0xc2 ≤ first && first ≤ 0xdf then (2, first - 0xc0, 0x80)
        else if 0xe0 ≤ first && first ≤ 0xef then (3, first - 0xe0, 0x800)
        else if 0xf0 ≤ first && first ≤ 0xf4 then (4, first - 0xf0, 0x10000)
        else (0, 0, 0)
      let span : Span := ⟨file.identity, offset, min (offset + max width 1) bytes.size⟩
      require (width != 0 && offset + width ≤ bytes.size) .invalidSource "invalid UTF-8 leading byte or truncated sequence" span
      let scalar ← (List.range (width - 1)).foldlM (init := initial) fun value index => do
        let byte := (bytes[offset + index + 1]!).toNat
        require (0x80 ≤ byte && byte ≤ 0xbf) .invalidSource "invalid UTF-8 continuation byte" span
        return value * 64 + byte - 0x80
      require (scalar ≥ minimum && scalar ≤ 0x10ffff && !(0xd800 ≤ scalar && scalar ≤ 0xdfff))
        .invalidSource "non-shortest or invalid UTF-8 scalar" span
      decode fuel (offset + width) (output.push ⟨scalar, offset, width⟩)
  let start := if bytes.size ≥ 3 && bytes[0]! == 0xef && bytes[1]! == 0xbb && bytes[2]! == 0xbf then 3 else 0
  decode (bytes.size + 1) start #[]

inductive TokenKind where
  | identifier (name : String)
  | number (spelling : String)
  | string (bytes : List UInt8) (byteString : Bool)
  | character (scalar : Nat) (byte : Bool)
  | lifetime (name : String)
  | label (name : String)
  | punctuation (spelling : String)
  | eof
  deriving BEq, Repr

structure Token where
  kind : TokenKind
  span : Span
  deriving Repr

def Token.spelling : Token → String
  | ⟨.identifier name, _⟩ | ⟨.number name, _⟩ | ⟨.punctuation name, _⟩ => name
  | ⟨.lifetime name, _⟩ => "'" ++ name
  | ⟨.label name, _⟩ => "@" ++ name
  | ⟨.eof, _⟩ => "<eof>"
  | _ => "<literal>"

def encodeScalar (scalar : Nat) : List UInt8 :=
  if scalar < 0x80 then [UInt8.ofNat scalar]
  else if scalar < 0x800 then [UInt8.ofNat (0xc0 + scalar / 64), UInt8.ofNat (0x80 + scalar % 64)]
  else if scalar < 0x10000 then [UInt8.ofNat (0xe0 + scalar / 4096),
    UInt8.ofNat (0x80 + scalar / 64 % 64), UInt8.ofNat (0x80 + scalar % 64)]
  else [UInt8.ofNat (0xf0 + scalar / 262144), UInt8.ofNat (0x80 + scalar / 4096 % 64),
    UInt8.ofNat (0x80 + scalar / 64 % 64), UInt8.ofNat (0x80 + scalar % 64)]

def lex (file : SourceFile) : Check (Array Token) := do
  let characters ← decodeSource file
  let scalar (index : Nat) := (characters[index]?).map (·.scalar) |>.getD 0
  let offset (index : Nat) := (characters[index]?).map (·.offset) |>.getD file.bytes.size
  let span (first last : Nat) : Span := ⟨file.identity, offset first, offset last⟩
  let text (first last : Nat) := String.ofList ((characters.toList.drop first).take (last - first) |>.map (fun c => Char.ofNat c.scalar))
  let rec runWhile : Nat → Nat → (Nat → Bool) → Nat
    | 0, cursor, _ => cursor
    | fuel + 1, cursor, predicate => if cursor < characters.size && predicate (scalar cursor) then runWhile fuel (cursor + 1) predicate else cursor
  let rec blockComment : Nat → Nat → Nat → Check Nat
    | 0, cursor, _ => reject .invalidSource "unterminated block comment" (span cursor cursor)
    | fuel + 1, cursor, depth =>
      if cursor ≥ characters.size then reject .invalidSource "unterminated block comment" (span cursor cursor)
      else if scalar cursor == 47 && scalar (cursor + 1) == 42 then blockComment fuel (cursor + 2) (depth + 1)
      else if scalar cursor == 42 && scalar (cursor + 1) == 47 then
        if depth == 1 then return cursor + 2 else blockComment fuel (cursor + 2) (depth - 1)
      else blockComment fuel (cursor + 1) depth
  let rec escape (fuel cursor : Nat) (byte : Bool) : Check (Nat × Nat) := do
    match fuel with
    | 0 => reject .resourceLimit "literal escape budget exhausted" (span cursor cursor)
    | fuel + 1 =>
      let code := scalar cursor
      if code == 110 then return (10, cursor + 1)
      if code == 114 then return (13, cursor + 1)
      if code == 116 then return (9, cursor + 1)
      if code == 48 then return (0, cursor + 1)
      if code == 92 || code == 39 || code == 34 then return (code, cursor + 1)
      if code == 120 then
        let a ← getRequired (hexDigit (scalar (cursor + 1))) .invalidSource "invalid hexadecimal escape" (span cursor (cursor + 3))
        let b ← getRequired (hexDigit (scalar (cursor + 2))) .invalidSource "invalid hexadecimal escape" (span cursor (cursor + 3))
        let value := a * 16 + b
        require (byte || value < 128) .invalidSource "text hexadecimal escapes are ASCII-only" (span cursor (cursor + 3))
        return (value, cursor + 3)
      if code == 117 && scalar (cursor + 1) == 123 then
        require (!byte) .invalidSource "Unicode escapes are not byte literals" (span cursor (cursor + 2))
        let end_ := runWhile fuel (cursor + 2) (fun n => (hexDigit n).isSome)
        require (end_ > cursor + 2 && scalar end_ == 125) .invalidSource "invalid Unicode escape" (span cursor end_)
        let value := ((characters.toList.drop (cursor + 2)).take (end_ - cursor - 2)).foldl
          (fun n character => n * 16 + (hexDigit character.scalar).getD 0) 0
        require (value ≤ 0x10ffff && !(0xd800 ≤ value && value ≤ 0xdfff)) .invalidSource "invalid Unicode scalar escape" (span cursor end_)
        return (value, end_ + 1)
      reject .invalidSource "unknown literal escape" (span cursor (cursor + 1))
  let rec quoted : Nat → Nat → Nat → Bool → List Nat → Check (List Nat × Nat)
    | 0, cursor, _, _, _ => reject .invalidSource "unterminated literal" (span cursor cursor)
    | fuel + 1, cursor, quote, byte, values => do
      require (cursor < characters.size) .invalidSource "unterminated literal" (span cursor cursor)
      if scalar cursor == quote then return (values, cursor + 1)
      let (value, next) ← if scalar cursor == 92 then escape fuel (cursor + 1) byte else pure (scalar cursor, cursor + 1)
      require (!byte || value < 256) .invalidSource "byte literal contains a non-byte scalar" (span cursor next)
      require (!byte || scalar cursor == 92 || value < 128) .invalidSource "non-ASCII byte content requires a numeric escape" (span cursor next)
      quoted fuel next quote byte (values ++ [value])
  let rec tokenize : Nat → Nat → Array Token → Check (Array Token)
    | 0, cursor, _ => reject .resourceLimit "source token budget exhausted" (span cursor cursor)
    | fuel + 1, cursor, output => do
      if cursor ≥ characters.size then return output.push ⟨.eof, span cursor cursor⟩
      let c := scalar cursor
      if c == 32 || c == 9 || c == 10 || c == 13 then tokenize fuel (cursor + 1) output else
      if c == 47 && scalar (cursor + 1) == 47 then
        tokenize fuel (runWhile fuel (cursor + 2) (fun n => n != 10 && n != 13)) output
      else if c == 47 && scalar (cursor + 1) == 42 then
        tokenize fuel (← blockComment fuel (cursor + 2) 1) output
      else if c == 34 || (c == 98 && scalar (cursor + 1) == 34) then
        let byte := c == 98
        let (values, next) ← quoted fuel (cursor + (if byte then 2 else 1)) 34 byte []
        let bytes := if byte then values.map UInt8.ofNat else values.flatMap encodeScalar
        tokenize fuel next (output.push ⟨.string bytes byte, span cursor next⟩)
      else if c == 39 || (c == 98 && scalar (cursor + 1) == 39) then
        let byte := c == 98
        let start := cursor + (if byte then 2 else 1)
        let nameEnd := runWhile fuel start identifierContinue
        if !byte && asciiLetter (scalar start) && scalar nameEnd != 39 then
          tokenize fuel nameEnd (output.push ⟨.lifetime (text start nameEnd), span cursor nameEnd⟩)
        else
          let (values, next) ← quoted fuel start 39 byte []
          require (values.length == 1) .invalidSource "character literal must contain exactly one scalar" (span cursor next)
          tokenize fuel next (output.push ⟨.character (values.headD 0) byte, span cursor next⟩)
      else if c == 64 then
        require (asciiLetter (scalar (cursor + 1))) .invalidSource "label sigil requires an identifier" (span cursor (cursor + 1))
        let end_ := runWhile fuel (cursor + 1) identifierContinue
        tokenize fuel end_ (output.push ⟨.label (text (cursor + 1) end_), span cursor end_⟩)
      else if asciiLetter c then
        let end_ := runWhile fuel cursor identifierContinue
        tokenize fuel end_ (output.push ⟨.identifier (text cursor end_), span cursor end_⟩)
      else if asciiDigit c then
        let rec numeric : Nat → Nat → Nat
          | 0, index => index
          | n + 1, index =>
            let value := scalar index
            if index < characters.size && (identifierContinue value ||
              (value == 46 && asciiDigit (scalar (index + 1))) ||
              ((value == 43 || value == 45) && (scalar (index - 1) == 101 || scalar (index - 1) == 69)))
            then numeric n (index + 1) else index
        let end_ := numeric fuel (cursor + 1)
        tokenize fuel end_ (output.push ⟨.number (text cursor end_), span cursor end_⟩)
      else
        require (c < 128) .invalidSource "identifiers are ASCII in this language version" (span cursor (cursor + 1))
        let two := text cursor (min characters.size (cursor + 2))
        let (spelling, next) := if ["::", "->", "=>", "..", "==", "!=", "<=", ">="].contains two
          then (two, cursor + 2) else (text cursor (cursor + 1), cursor + 1)
        tokenize fuel next (output.push ⟨.punctuation spelling, span cursor next⟩)
  tokenize (characters.size * 4 + 1) 0 #[]

def parseScalarType (name : String) : Option ScalarType :=
  match name with
  | "u8" => some (.integer false .w8) | "u16" => some (.integer false .w16)
  | "u32" => some (.integer false .w32) | "u64" => some (.integer false .w64)
  | "u128" => some (.integer false .w128) | "usize" => some (.integer false .pointer)
  | "i8" => some (.integer true .w8) | "i16" => some (.integer true .w16)
  | "i32" => some (.integer true .w32) | "i64" => some (.integer true .w64)
  | "i128" => some (.integer true .w128) | "isize" => some (.integer true .pointer)
  | "f32" => some (.floating .w32) | "f64" => some (.floating .w64)
  | "char" => some .character | _ => none

def numericLiteral (spelling : String) (span : Span) : Check Literal := do
  let suffixes := ["usize", "isize", "u128", "i128", "u64", "i64", "u32", "i32", "u16", "i16", "u8", "i8", "f32", "f64"]
  let suffix := suffixes.find? (fun (suffix : String) => spelling.endsWith suffix)
  let digits := match suffix with | none => spelling | some suffix => (spelling.dropEnd suffix.length).toString
  let chars := digits.toList
  for (c, index) in chars.zipIdx do
    if c == '_' then
      require (index > 0 && index + 1 < chars.length && chars[index - 1]! != '_' && chars[index + 1]! != '_')
        .invalidSource "numeric underscores must separate digits" span
  let digits := digits.replace "_" ""
  let floating := suffix == some "f32" || suffix == some "f64" ||
    ((!digits.startsWith "0x") && (digits.contains '.' || digits.contains 'e' || digits.contains 'E'))
  if floating then
    let parts := digits.replace "E" "e" |>.splitOn "e"
    require (parts.length ≤ 2) .invalidSource "malformed floating exponent" span
    let coefficient := parts.headD ""
    let exponent ← if parts.length == 2 then
        getRequired ((parts[1]!).toInt?) .invalidSource "invalid decimal exponent" span
      else pure 0
    let fractional := coefficient.splitOn "."
    require (fractional.length ≤ 2) .invalidSource "malformed floating fraction" span
    let fractionalDigits := if fractional.length == 2 then (fractional[1]!).length else 0
    let significand ← getRequired ((coefficient.replace "." "").toNat?) .invalidSource "invalid floating significand" span
    let width := match suffix with | some "f32" => some .w32 | some "f64" => some .w64 | _ => none
    return .decimalFloat false significand (exponent - Int.ofNat fractionalDigits) width
  else
    let (base, digits) := if digits.startsWith "0x" then (16, digits.drop 2 |>.toString)
      else if digits.startsWith "0o" then (8, digits.drop 2 |>.toString)
      else if digits.startsWith "0b" then (2, digits.drop 2 |>.toString) else (10, digits)
    require (!digits.isEmpty) .invalidSource "numeric literal has no digits" span
    let magnitude ← digits.toList.foldlM (init := 0) fun value char => do
      let digit ← getRequired (hexDigit char.toNat) .invalidSource "invalid integer digit" span
      require (digit < base) .invalidSource "digit is not valid in the selected base" span
      return value * base + digit
    return .integer magnitude (suffix.bind parseScalarType) false

end Glorious.Semantics
