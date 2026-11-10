import Glorious.Bytecode.Ast

/-!
# Binary encoding of bytecode

Numbers are little-endian base-128 with a continuation bit; signed integers are
zigzag-coded first. A list is its length followed by its items. Every
alternative starts with a one-byte tag.
-/

namespace Glorious.Bytecode.Encode

/-- Bytes as numbers below 256, so that statements about the format need no
machine-word arithmetic. -/
abbrev Bytes := List Nat

def nat (n : Nat) : Bytes :=
  if n < 128 then [n]
  else (n % 128 + 128) :: nat (n / 128)
termination_by n
decreasing_by omega

def int : Int → Bytes
  | .ofNat m => nat (2 * m)
  | .negSucc m => nat (2 * m + 1)

def list {α : Type} (item : α → Bytes) (xs : List α) : Bytes :=
  nat xs.length ++ xs.flatMap item

def atom : Atom → Bytes
  | .var i => 0 :: nat i
  | .int n => 1 :: int n

def place (pl : Place) : Bytes := nat pl.var ++ list nat pl.path

def prim : Prim → Bytes
  | .intAdd => [0]
  | .intSub => [1]
  | .intMul => [2]
  | .intLt => [3]
  | .intEq => [4]

def rhs : Rhs → Bytes
  | .atom a => 0 :: atom a
  | .prim p args => 1 :: prim p ++ list atom args
  | .construct tag args => 2 :: nat tag ++ list atom args
  | .place pl => 3 :: place pl
  | .closure fn captures => 4 :: nat fn ++ list atom captures

def pair (p : Nat × Nat) : Bytes := nat p.1 ++ nat p.2

def memOp : MemOp → Bytes
  | .alloc => [0]
  | .load => [1]
  | .store => [2]
  | .free => [3]

def instr : Instr → Bytes
  | .op r => 0 :: rhs r
  | .call f args => 1 :: atom f ++ list atom args
  | .tail f args => 2 :: atom f ++ list atom args
  | .ret a => 3 :: atom a
  | .handle ret ops captures thunk =>
    4 :: nat ret ++ list pair ops ++ list atom captures ++ atom thunk
  | .handleTail ret ops captures thunk =>
    5 :: nat ret ++ list pair ops ++ list atom captures ++ atom thunk
  | .raise op args => 6 :: nat op ++ list atom args
  | .perform op args => 7 :: nat op ++ list atom args
  | .label thunk => 8 :: atom thunk
  | .labelTail thunk => 9 :: atom thunk
  | .guard cleanup thunk => 10 :: atom cleanup ++ atom thunk
  | .guardTail cleanup thunk => 11 :: atom cleanup ++ atom thunk
  | .cancel k => 12 :: atom k
  | .host id args => 13 :: nat id ++ list atom args
  | .testCtor pl tag arity fail => 14 :: place pl ++ nat tag ++ nat arity ++ nat fail
  | .testInt pl n fail => 15 :: place pl ++ int n ++ nat fail
  | .mem op args => 16 :: memOp op ++ list atom args

def code (c : Code) : Bytes := list instr c

def program (p : Program) : Bytes := list (fun f => code f.code) p.fns ++ code p.main

def string (s : String) : Bytes := list (fun b => [b.toNat]) s.toUTF8.toList

/-- A bytecode file: the magic `GLBC`, a format version, the constructor names
used to print values, and the program. -/
def file (ctorNames : List String) (p : Program) : Bytes :=
  [0x47, 0x4C, 0x42, 0x43, 1] ++ list string ctorNames ++ program p

end Glorious.Bytecode.Encode
