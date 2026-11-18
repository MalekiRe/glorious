module

/-!
# Lexer
-/

public section

namespace Glorious.Syntax

inductive Tok where
  | ident (s : String)
  | int (n : Nat)
  /-- A whole number with the type it is written to have, `5u8`. -/
  | typed (n : Nat) (suffix : String)
  /-- A number with a point or an exponent, `1.5`, `2e-3`, `1.5f32`: its
  digits as a whole number, the power of ten they are multiplied by, and the
  type it is written to have, if any. -/
  | float (digits : Nat) (exp10 : Int) (suffix : String)
  /-- A character, `'a'`: its code. -/
  | char (code : Nat)
  /-- A text, `"abc"`: the codes of its characters. -/
  | str (codes : List Nat)
  /-- Bytes, `b"abc"`: each below 256. -/
  | bytes (codes : List Nat)
  /-- A symbolic operator such as `+` or `==`. -/
  | op (s : String)
  /-- Punctuation: `( ) { } [ ] , ; . @ : :: = => ->`. -/
  | punct (s : String)
  | eof
  deriving BEq, Inhabited

structure Token where
  tok : Tok
  line : Nat
  col : Nat
  deriving Inhabited

def Tok.describe : Tok → String
  | .ident s => s!"`{s}`"
  | .int n => s!"`{n}`"
  | .typed n suffix => s!"`{n}{suffix}`"
  | .float _ _ _ => "a number"
  | .char _ => "a character"
  | .str _ => "a text"
  | .bytes _ => "bytes"
  | .op s => s!"`{s}`"
  | .punct s => s!"`{s}`"
  | .eof => "end of input"

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

private def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_'

private def isOpChar : Char → Bool
  | '+' | '-' | '*' | '/' | '<' | '>' | '=' | '!' | '&' | '|' | '%' | '^' | '~' | '?' => true
  | _ => false

/-- A punctuation character's token text, one string for every use of it. -/
private def punctText : Char → Option String
  | '(' => some "(" | ')' => some ")" | '{' => some "{" | '}' => some "}"
  | '[' => some "[" | ']' => some "]" | ',' => some "," | ';' => some ";"
  | '.' => some "." | '@' => some "@" | '#' => some "#"
  | _ => none

/-- An operator of one character's text, one string for every use of it. -/
private def opText : Char → String
  | '+' => "+" | '-' => "-" | '*' => "*" | '/' => "/" | '<' => "<" | '>' => ">"
  | '=' => "=" | '!' => "!" | '&' => "&" | '|' => "|" | '%' => "%" | '^' => "^"
  | '~' => "~" | '?' => "?" | c => String.singleton c

/-- The character at `i`, or `'\x00'` past the end: no option made per look. -/
@[inline] private def charAt (cs : Array Char) (i : Nat) : Char := cs.getD i '\x00'

private def slice (cs : Array Char) (i j : Nat) : String :=
  String.ofList (cs.extract i j).toList

private partial def spanWhile (cs : Array Char) (p : Char → Bool) (i : Nat) : Nat :=
  if i < cs.size && p (charAt cs i) then spanWhile cs p (i + 1) else i

private def digitOf (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The digits of a number in a base from `i`, `_` between them allowed: the
number, how many digits it has, and where they end. -/
private partial def lexDigits (cs : Array Char) (base : Nat) (i : Nat) (n count : Nat) :
    Nat × Nat × Nat :=
  if i ≥ cs.size then (n, count, i) else
  match charAt cs i with
  | '_' =>
    -- Only between digits.
    match digitOf (charAt cs (i + 1)) with
    | some d => if d < base && count > 0 then lexDigits cs base (i + 1) n count else (n, count, i)
    | none => (n, count, i)
  | c =>
    match digitOf c with
    | some d => if d < base then lexDigits cs base (i + 1) (n * base + d) (count + 1) else (n, count, i)
    | none => (n, count, i)

/-- What is written after `\` in a character or a text: the code it stands
for and where it ends. -/
private partial def lexEscape (cs : Array Char) (i line col : Nat) (byte : Bool := false) :
    Except String (Nat × Nat) :=
  match charAt cs i with
  | 'n' => pure (10, i + 1)
  | 'r' => pure (13, i + 1)
  | 't' => pure (9, i + 1)
  | '0' => pure (0, i + 1)
  | '\\' => pure (92, i + 1)
  | '\'' => pure (39, i + 1)
  | '"' => pure (34, i + 1)
  | 'x' =>
    match digitOf (charAt cs (i + 1)), digitOf (charAt cs (i + 2)) with
    | some a, some b =>
      -- (a byte may be any code that fits one)
      if a * 16 + b < 128 || byte then pure (a * 16 + b, i + 3)
      else throw s!"{line}:{col}: `\\x` is for the codes below 80; write `\\u\{..}`"
    | _, _ => throw s!"{line}:{col}: `\\x` is followed by two digits in base 16"
  | 'u' =>
    if charAt cs (i + 1) != '{' then throw s!"{line}:{col}: `\\u` is followed by `\{`, digits in base 16, and `}`"
    else
      let (n, count, j) := lexDigits cs 16 (i + 2) 0 0
      if count == 0 || charAt cs (j) != '}' then
        throw s!"{line}:{col}: `\\u` is followed by `\{`, digits in base 16, and `}`"
      else if n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then
        throw s!"{line}:{col}: `\\u\{..}` is not the code of a character"
      else pure (n, j + 1)
  | _ => throw s!"{line}:{col}: unknown escape after `\\`"

/-- The characters of a text from `i` up to its closing `"`: their codes, and
where the text ends. -/
private partial def lexText (cs : Array Char) (i line col : Nat) (acc : Array Nat)
    (byte : Bool := false) : Except String (List Nat × Nat) :=
  if i ≥ cs.size then throw s!"{line}:{col}: this text is not closed" else
  match charAt cs i with
  | '\n' => throw s!"{line}:{col}: this text is not closed on its line (`\\n` is a new line)"
  | '"' => pure (acc.toList, i + 1)
  | '\\' => do
    let (code, j) ← lexEscape cs (i + 1) line col byte
    lexText cs j line col (acc.push code) byte
  | c => lexText cs (i + 1) line col (acc.push c.toNat) byte

/-- Past a `/* .. */` comment whose inside starts at `i`, `depth` deep:
where it ends, and the line and column there. -/
private partial def skipComment (cs : Array Char) (i line col depth : Nat) :
    Option (Nat × Nat × Nat) :=
  if i ≥ cs.size then none else
  match charAt cs i, charAt cs (i + 1) with
  | '*', '/' =>
    if depth == 1 then some (i + 2, line, col + 2) else skipComment cs (i + 2) line (col + 2) (depth - 1)
  | '/', '*' => skipComment cs (i + 2) line (col + 2) (depth + 1)
  | '\n', _ => skipComment cs (i + 1) (line + 1) 1 depth
  | _, _ => skipComment cs (i + 1) line (col + 1) depth

private partial def lexLoop (cs : Array Char) (i line col : Nat) (acc : Array Token) :
    Except String (Array Token) :=
  if i ≥ cs.size then pure (acc.push ⟨.eof, line, col⟩) else
    let c := charAt cs i
    if c == '\n' then lexLoop cs (i + 1) (line + 1) 1 acc
    else if c.isWhitespace then lexLoop cs (i + 1) line (col + 1) acc
    else if c == '/' && charAt cs (i + 1) == '/' then
      lexLoop cs (spanWhile cs (· != '\n') i) line col acc
    else if c == '/' && charAt cs (i + 1) == '*' then
      -- `/* .. */`, which may have others inside it.
      match skipComment cs (i + 2) line (col + 2) 1 with
      | some (j, line', col') => lexLoop cs j line' col' acc
      | none => throw s!"{line}:{col}: this comment is not closed"
    else if c == 'b' && charAt cs (i + 1) == '"' then
      -- `b"abc"`: bytes, each a character below 128 or `\xNN`.
      match lexText cs (i + 2) line col #[] true with
      | .ok (codes, j) =>
        if codes.any (· > 255) || ((cs.extract (i + 2) j).any fun ch => ch.toNat > 127) then
          throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
        else lexLoop cs j line (col + (j - i)) (acc.push ⟨.bytes codes, line, col⟩)
      | .error e => throw e
    else if c == 'b' && charAt cs (i + 1) == '\'' then
      -- `b'x'`: a byte, which is a `u8`.
      let read : Except String (Nat × Nat) :=
        if charAt cs (i + 2) == '\\' then lexEscape cs (i + 3) line col true
        else if i + 2 ≥ cs.size then throw s!"{line}:{col}: a byte is closed with `'`"
        else
          let ch := charAt cs (i + 2)
          if ch.toNat > 127 then throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
          else pure (ch.toNat, i + 3)
      match read with
      | .ok (code, j) =>
        if charAt cs (j) != '\'' then throw s!"{line}:{col}: a byte is closed with `'`"
        else if code > 255 then throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
        else lexLoop cs (j + 1) line (col + (j + 1 - i)) (acc.push ⟨.typed code "u8", line, col⟩)
      | .error e => throw e
    else if c.isDigit then
      let next := charAt cs (i + 1)
      let base := if c == '0' && next == 'x' then 16 else if c == '0' && next == 'b' then 2
        else if c == '0' && next == 'o' then 8 else 10
      let start := if base == 10 then i else i + 2
      let (n, count, j) := lexDigits cs base start 0 0
      if count == 0 then throw s!"{line}:{col}: a number needs a digit after its base"
      else
        -- A point and digits after it, unless this is a field's number: in
        -- `p.0.1` the `0.1` is two fields.
        let afterPoint := (acc.back?.map (·.tok)) == some (Tok.punct ".")
        let (digits, exp10, j, floating) :=
          if base == 10 && !afterPoint && charAt cs (j) == '.' && (charAt cs (j + 1)).isDigit then
            let (m, places, k) := lexDigits cs 10 (j + 1) n 0
            (m, -(places : Int), k, true)
          else (n, (0 : Int), j, false)
        -- An exponent.
        let (exp10, j, floating) :=
          if base == 10 && !afterPoint && (charAt cs (j) == 'e' || charAt cs (j) == 'E') then
            let signed := charAt cs (j + 1) == '-' || charAt cs (j + 1) == '+'
            let from_ := if signed then j + 2 else j + 1
            let (e, count, k) := lexDigits cs 10 from_ 0 0
            if count == 0 then (exp10, j, floating)
            else (exp10 + (if charAt cs (j + 1) == '-' then -(e : Int) else (e : Int)), k, true)
          else (exp10, j, floating)
        -- The type, written straight after.
        let k := if isIdentStart (charAt cs j) then spanWhile cs isIdentRest j else j
        let suffix := slice cs j k
        let tok := if floating || suffix == "f32" || suffix == "f64" then Tok.float digits exp10 suffix
          else if suffix.isEmpty then Tok.int digits
          else Tok.typed digits suffix
        lexLoop cs k line (col + (k - i)) (acc.push ⟨tok, line, col⟩)
    else if isIdentStart c then
      let j := spanWhile cs isIdentRest i
      lexLoop cs j line (col + (j - i)) (acc.push ⟨.ident (slice cs i j), line, col⟩)
    else if c == '"' then
      match lexText cs (i + 1) line col #[] with
      | .ok (codes, j) => lexLoop cs j line (col + (j - i)) (acc.push ⟨.str codes, line, col⟩)
      | .error e => throw e
    else if c == '\'' && charAt cs (i + 1) == '\\' then
      match lexEscape cs (i + 2) line col with
      | .ok (code, j) =>
        if charAt cs (j) == '\'' then lexLoop cs (j + 1) line (col + (j + 1 - i)) (acc.push ⟨.char code, line, col⟩)
        else throw s!"{line}:{col}: a character is closed with `'`"
      | .error e => throw e
    else if c == '\'' && charAt cs (i + 2) == '\'' && i + 1 < cs.size then
      -- `'a'` is a character; `'a` with no `'` after it is a lifetime.
      lexLoop cs (i + 3) line (col + 3) (acc.push ⟨.char ((charAt cs (i + 1)).toNat), line, col⟩)
    else if c == '\'' && isIdentStart (charAt cs (i + 1)) then
      -- A lifetime, `'a`: a name that keeps its mark.
      let j := spanWhile cs isIdentRest (i + 1)
      lexLoop cs j line (col + (j - i)) (acc.push ⟨.ident (slice cs i j), line, col⟩)
    else if isOpChar c then
      let j := spanWhile cs isOpChar i
      let s := slice cs i j
      -- `>>` closes two type argument lists, `<<` opens a list whose first
      -- argument is a qualified path (`Option<<T as Tr>::Out>`); neither is
      -- one operator.
      if j > i + 1 && ((cs.extract i j).all (· == '>') || (cs.extract i j).all (· == '<')) then
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op (opText c), line, col⟩)
      -- `<&` opens a type argument list with a reference in it.
      else if j > i + 1 && c == '<' && charAt cs (i + 1) == '&' then
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op "<", line, col⟩)
      -- `*<T as Tr>::f(..)`, `&<..>`, `!<..>`, `-<..>`: a prefix operator
      -- on a qualified path.
      else if j > i + 1 && (c == '*' || c == '&' || c == '!' || c == '-') && charAt cs (i + 1) == '<' then
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op (opText c), line, col⟩)
      else
        let s := if j == i + 1 then opText c else s
        let tok := if s == "=" || s == "=>" || s == "->" then Tok.punct s else Tok.op s
        lexLoop cs j line (col + (j - i)) (acc.push ⟨tok, line, col⟩)
    else if c == ':' && charAt cs (i + 1) == ':' then
      lexLoop cs (i + 2) line (col + 2) (acc.push ⟨.punct "::", line, col⟩)
    else if c == ':' then
      lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.punct ":", line, col⟩)
    else match punctText c with
      | some p => lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.punct p, line, col⟩)
      | none => throw s!"{line}:{col}: unexpected character `{c}`"

def lex (src : String) : Except String (Array Token) :=
  -- A byte-order mark at the very start is not part of the text.
  let cs := src.foldl (fun (a : Array Char) c => a.push c) (Array.mkEmpty src.utf8ByteSize)
  lexLoop cs (if charAt cs 0 == '\uFEFF' then 1 else 0) 1 1 #[]

end Glorious.Syntax
