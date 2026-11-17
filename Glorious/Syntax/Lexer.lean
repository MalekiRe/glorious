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

private def isOpChar (c : Char) : Bool := "+-*/<>=!&|%^~?".toList.contains c

private def isPunctChar (c : Char) : Bool := "(){}[],;.@#".toList.contains c

private def slice (cs : Array Char) (i j : Nat) : String :=
  (cs.extract i j).foldl (fun s c => s.push c) ""

private partial def spanWhile (cs : Array Char) (p : Char → Bool) (i : Nat) : Nat :=
  match cs[i]? with
  | some c => if p c then spanWhile cs p (i + 1) else i
  | none => i

private def digitOf (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The digits of a number in a base from `i`, `_` between them allowed: the
number, how many digits it has, and where they end. -/
private partial def lexDigits (cs : Array Char) (base : Nat) (i : Nat) (n count : Nat) :
    Nat × Nat × Nat :=
  match cs[i]? with
  | some '_' =>
    -- Only between digits.
    match cs[i + 1]?.bind digitOf with
    | some d => if d < base && count > 0 then lexDigits cs base (i + 1) n count else (n, count, i)
    | none => (n, count, i)
  | some c =>
    match digitOf c with
    | some d => if d < base then lexDigits cs base (i + 1) (n * base + d) (count + 1) else (n, count, i)
    | none => (n, count, i)
  | none => (n, count, i)

/-- What is written after `\` in a character or a text: the code it stands
for and where it ends. -/
private partial def lexEscape (cs : Array Char) (i line col : Nat) (byte : Bool := false) :
    Except String (Nat × Nat) :=
  match cs[i]? with
  | some 'n' => pure (10, i + 1)
  | some 'r' => pure (13, i + 1)
  | some 't' => pure (9, i + 1)
  | some '0' => pure (0, i + 1)
  | some '\\' => pure (92, i + 1)
  | some '\'' => pure (39, i + 1)
  | some '"' => pure (34, i + 1)
  | some 'x' =>
    match cs[i + 1]?.bind digitOf, cs[i + 2]?.bind digitOf with
    | some a, some b =>
      -- (a byte may be any code that fits one)
      if a * 16 + b < 128 || byte then pure (a * 16 + b, i + 3)
      else throw s!"{line}:{col}: `\\x` is for the codes below 80; write `\\u\{..}`"
    | _, _ => throw s!"{line}:{col}: `\\x` is followed by two digits in base 16"
  | some 'u' =>
    if cs[i + 1]? != some '{' then throw s!"{line}:{col}: `\\u` is followed by `\{`, digits in base 16, and `}`"
    else
      let (n, count, j) := lexDigits cs 16 (i + 2) 0 0
      if count == 0 || cs[j]? != some '}' then
        throw s!"{line}:{col}: `\\u` is followed by `\{`, digits in base 16, and `}`"
      else if n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then
        throw s!"{line}:{col}: `\\u\{..}` is not the code of a character"
      else pure (n, j + 1)
  | _ => throw s!"{line}:{col}: unknown escape after `\\`"

/-- The characters of a text from `i` up to its closing `"`: their codes, and
where the text ends. -/
private partial def lexText (cs : Array Char) (i line col : Nat) (acc : Array Nat)
    (byte : Bool := false) : Except String (List Nat × Nat) :=
  match cs[i]? with
  | none => throw s!"{line}:{col}: this text is not closed"
  | some '\n' => throw s!"{line}:{col}: this text is not closed on its line (`\\n` is a new line)"
  | some '"' => pure (acc.toList, i + 1)
  | some '\\' => do
    let (code, j) ← lexEscape cs (i + 1) line col byte
    lexText cs j line col (acc.push code) byte
  | some c => lexText cs (i + 1) line col (acc.push c.toNat) byte

/-- Past a `/* .. */` comment whose inside starts at `i`, `depth` deep:
where it ends, and the line and column there. -/
private partial def skipComment (cs : Array Char) (i line col depth : Nat) :
    Option (Nat × Nat × Nat) :=
  match cs[i]?, cs[i + 1]? with
  | none, _ => none
  | some '*', some '/' =>
    if depth == 1 then some (i + 2, line, col + 2) else skipComment cs (i + 2) line (col + 2) (depth - 1)
  | some '/', some '*' => skipComment cs (i + 2) line (col + 2) (depth + 1)
  | some '\n', _ => skipComment cs (i + 1) (line + 1) 1 depth
  | some _, _ => skipComment cs (i + 1) line (col + 1) depth

private partial def lexLoop (cs : Array Char) (i line col : Nat) (acc : Array Token) :
    Except String (Array Token) :=
  match cs[i]? with
  | none => pure (acc.push ⟨.eof, line, col⟩)
  | some c =>
    if c == '\n' then lexLoop cs (i + 1) (line + 1) 1 acc
    else if c.isWhitespace then lexLoop cs (i + 1) line (col + 1) acc
    else if c == '/' && cs[i + 1]? == some '/' then
      lexLoop cs (spanWhile cs (· != '\n') i) line col acc
    else if c == '/' && cs[i + 1]? == some '*' then
      -- `/* .. */`, which may have others inside it.
      match skipComment cs (i + 2) line (col + 2) 1 with
      | some (j, line', col') => lexLoop cs j line' col' acc
      | none => throw s!"{line}:{col}: this comment is not closed"
    else if c == 'b' && cs[i + 1]? == some '"' then
      -- `b"abc"`: bytes, each a character below 128 or `\xNN`.
      match lexText cs (i + 2) line col #[] true with
      | .ok (codes, j) =>
        if codes.any (· > 255) || ((cs.extract (i + 2) j).any fun ch => ch.toNat > 127) then
          throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
        else lexLoop cs j line (col + (j - i)) (acc.push ⟨.bytes codes, line, col⟩)
      | .error e => throw e
    else if c == 'b' && cs[i + 1]? == some '\'' then
      -- `b'x'`: a byte, which is a `u8`.
      let read : Except String (Nat × Nat) :=
        if cs[i + 2]? == some '\\' then lexEscape cs (i + 3) line col true
        else match cs[i + 2]? with
          | some ch =>
            if ch.toNat > 127 then throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
            else pure (ch.toNat, i + 3)
          | none => throw s!"{line}:{col}: a byte is closed with `'`"
      match read with
      | .ok (code, j) =>
        if cs[j]? != some '\'' then throw s!"{line}:{col}: a byte is closed with `'`"
        else if code > 255 then throw s!"{line}:{col}: a byte is a character below 128, or `\\xNN`"
        else lexLoop cs (j + 1) line (col + (j + 1 - i)) (acc.push ⟨.typed code "u8", line, col⟩)
      | .error e => throw e
    else if c.isDigit then
      let next := cs[i + 1]?
      let base := if c == '0' && next == some 'x' then 16 else if c == '0' && next == some 'b' then 2
        else if c == '0' && next == some 'o' then 8 else 10
      let start := if base == 10 then i else i + 2
      let (n, count, j) := lexDigits cs base start 0 0
      if count == 0 then throw s!"{line}:{col}: a number needs a digit after its base"
      else
        -- A point and digits after it, unless this is a field's number: in
        -- `p.0.1` the `0.1` is two fields.
        let afterPoint := (acc.back?.map (·.tok)) == some (Tok.punct ".")
        let (digits, exp10, j, floating) :=
          if base == 10 && !afterPoint && cs[j]? == some '.' && ((cs[j + 1]?.map Char.isDigit).getD false) then
            let (m, places, k) := lexDigits cs 10 (j + 1) n 0
            (m, -(places : Int), k, true)
          else (n, (0 : Int), j, false)
        -- An exponent.
        let (exp10, j, floating) :=
          if base == 10 && !afterPoint && (cs[j]? == some 'e' || cs[j]? == some 'E') then
            let signed := cs[j + 1]? == some '-' || cs[j + 1]? == some '+'
            let from_ := if signed then j + 2 else j + 1
            let (e, count, k) := lexDigits cs 10 from_ 0 0
            if count == 0 then (exp10, j, floating)
            else (exp10 + (if cs[j + 1]? == some '-' then -(e : Int) else (e : Int)), k, true)
          else (exp10, j, floating)
        -- The type, written straight after.
        let k := if (cs[j]?.map isIdentStart).getD false then spanWhile cs isIdentRest j else j
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
    else if c == '\'' && cs[i + 1]? == some '\\' then
      match lexEscape cs (i + 2) line col with
      | .ok (code, j) =>
        if cs[j]? == some '\'' then lexLoop cs (j + 1) line (col + (j + 1 - i)) (acc.push ⟨.char code, line, col⟩)
        else throw s!"{line}:{col}: a character is closed with `'`"
      | .error e => throw e
    else if c == '\'' && cs[i + 2]? == some '\'' && cs[i + 1]?.isSome then
      -- `'a'` is a character; `'a` with no `'` after it is a lifetime.
      lexLoop cs (i + 3) line (col + 3) (acc.push ⟨.char ((cs[i + 1]?.getD ' ').toNat), line, col⟩)
    else if c == '\'' && (cs[i + 1]?.map isIdentStart).getD false then
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
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op (String.singleton c), line, col⟩)
      -- `<&` opens a type argument list with a reference in it.
      else if j > i + 1 && c == '<' && cs[i + 1]? == some '&' then
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op "<", line, col⟩)
      -- `*<T as Tr>::f(..)`, `&<..>`, `!<..>`, `-<..>`: a prefix operator
      -- on a qualified path.
      else if j > i + 1 && "*&!-".toList.contains c && cs[i + 1]? == some '<' then
        lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.op (String.singleton c), line, col⟩)
      else
        let tok := if ["=", "=>", "->"].contains s then Tok.punct s else Tok.op s
        lexLoop cs j line (col + (j - i)) (acc.push ⟨tok, line, col⟩)
    else if c == ':' && cs[i + 1]? == some ':' then
      lexLoop cs (i + 2) line (col + 2) (acc.push ⟨.punct "::", line, col⟩)
    else if c == ':' then
      lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.punct ":", line, col⟩)
    else if isPunctChar c then
      lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.punct (String.singleton c), line, col⟩)
    else throw s!"{line}:{col}: unexpected character `{c}`"

def lex (src : String) : Except String (Array Token) :=
  -- A byte-order mark at the very start is not part of the text.
  let cs := src.toList.toArray
  lexLoop cs (if cs[0]? == some '\uFEFF' then 1 else 0) 1 1 #[]

end Glorious.Syntax
