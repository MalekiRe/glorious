/-!
# Lexer
-/

namespace Glorious.Syntax

inductive Tok where
  | ident (s : String)
  | int (n : Nat)
  /-- A symbolic operator such as `+` or `==`. -/
  | op (s : String)
  /-- Punctuation: `( ) { } [ ] , ; . @ :: = => ->`. -/
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
  | .op s => s!"`{s}`"
  | .punct s => s!"`{s}`"
  | .eof => "end of input"

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

private def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_'

private def isOpChar (c : Char) : Bool := "+-*/<>=!&|%^~?".toList.contains c

private def isPunctChar (c : Char) : Bool := "(){}[],;.@".toList.contains c

private def slice (cs : Array Char) (i j : Nat) : String :=
  (cs.extract i j).foldl (fun s c => s.push c) ""

private partial def spanWhile (cs : Array Char) (p : Char → Bool) (i : Nat) : Nat :=
  match cs[i]? with
  | some c => if p c then spanWhile cs p (i + 1) else i
  | none => i

private partial def lexLoop (cs : Array Char) (i line col : Nat) (acc : Array Token) :
    Except String (Array Token) :=
  match cs[i]? with
  | none => pure (acc.push ⟨.eof, line, col⟩)
  | some c =>
    if c == '\n' then lexLoop cs (i + 1) (line + 1) 1 acc
    else if c.isWhitespace then lexLoop cs (i + 1) line (col + 1) acc
    else if c == '/' && cs[i + 1]? == some '/' then
      lexLoop cs (spanWhile cs (· != '\n') i) line col acc
    else if c.isDigit then
      let j := spanWhile cs Char.isDigit i
      let n := (cs.extract i j).foldl (fun n d => n * 10 + (d.toNat - '0'.toNat)) 0
      lexLoop cs j line (col + (j - i)) (acc.push ⟨.int n, line, col⟩)
    else if isIdentStart c then
      let j := spanWhile cs isIdentRest i
      lexLoop cs j line (col + (j - i)) (acc.push ⟨.ident (slice cs i j), line, col⟩)
    else if isOpChar c then
      let j := spanWhile cs isOpChar i
      let s := slice cs i j
      let tok := if ["=", "=>", "->"].contains s then Tok.punct s else Tok.op s
      lexLoop cs j line (col + (j - i)) (acc.push ⟨tok, line, col⟩)
    else if c == ':' && cs[i + 1]? == some ':' then
      lexLoop cs (i + 2) line (col + 2) (acc.push ⟨.punct "::", line, col⟩)
    else if isPunctChar c then
      lexLoop cs (i + 1) line (col + 1) (acc.push ⟨.punct (String.singleton c), line, col⟩)
    else throw s!"{line}:{col}: unexpected character `{c}`"

def lex (src : String) : Except String (Array Token) :=
  lexLoop src.toList.toArray 0 1 1 #[]

end Glorious.Syntax
