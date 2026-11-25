module

public import Glorious.Bytecode.Ast

/-!
# Binary encoding of bytecode

Numbers are little-endian base-128 with a continuation bit; signed integers are
zigzag-coded first. A list is its length followed by its items. Every
alternative starts with a one-byte tag.
-/

@[expose] public section

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
  | .intDiv => [5]
  | .intRem => [6]
  | .intFit => [7]
  | .f64Add => [8]
  | .f64Sub => [9]
  | .f64Mul => [10]
  | .f64Div => [11]
  | .f64Lt => [12]
  | .f64Eq => [13]
  | .f64OfInt => [14]
  | .f64ToInt => [15]
  | .f64Narrow => [16]
  | .f64Widen => [17]
  | .f64OfDecimal => [18]
  | .f64Digits => [19]
  | .f64Exp10 => [20]
  | .f64Sqrt => [21]
  | .f64Round => [22]
  | .wideAdd => [23]
  | .wideSub => [24]
  | .wideMul => [25]
  | .intAnd => [26]
  | .intOr => [27]
  | .intXor => [28]
  | .intShl => [29]
  | .intShr => [30]
  | .uwAdd => [31]
  | .uwSub => [32]
  | .uwMul => [33]
  | .uwDiv => [34]
  | .uwRem => [35]
  | .uwLt => [36]
  | .uwShl => [37]
  | .uwShr => [38]
  | .intBelow => [39]
  | .cast b into => 45 :: int b ++ [if into then 1 else 0]
  | .fixed op => 46 :: nat op

def rhs : Rhs → Bytes
  | .atom a => 0 :: atom a
  | .prim p args => 1 :: prim p ++ list atom args
  | .construct tag args => 2 :: nat tag ++ list atom args
  | .place pl => 3 :: place pl
  | .closure fn captures => 4 :: nat fn ++ list atom captures
  | .rebind a fn => 5 :: atom a ++ nat fn

def pair (p : Nat × Nat) : Bytes := nat p.1 ++ nat p.2

mutual

/-- A layout (`Lay`). -/
partial def lay : Lay → Bytes
  | .int n signed => 0 :: nat n ++ [if signed then 1 else 0]
  | .fields tag fs => 1 :: nat tag ++ laidFields fs
  | .tagged cs => 2 :: nat cs.length ++ cs.flatMap fun (tag, fs) => nat tag ++ laidFields fs
  | .addr => [3]
  | .held => [4]
  | .nothing => [5]

partial def laidFields (fs : List (Nat × Lay)) : Bytes :=
  nat fs.length ++ fs.flatMap fun (at_, l) => nat at_ ++ lay l

end

/-- A layout with its size and alignment, the layout by its place in the
file's table (`layTable`). -/
def laid (ix : Lay → Nat) (l : Laid) : Bytes := nat l.size ++ nat l.align ++ nat (ix l.lay)

/-- An access of memory; one at a layout names it by its place in the table. -/
def memOp (ix : Lay → Nat) : MemOp → Bytes
  | .load => [0]
  | .store => [1]
  | .swap => [2]
  | .tag => [3]
  | .focus => [4]
  | .alloc => [5]
  | .free => [6]
  | .readBits => [7]
  | .writeBits => [8]
  | .copy => [9]
  | .sizeOf => [15]
  | .alignOf => [16]
  | .deref => [17]
  | .staticAt => [18]
  | .addressOf => [19]
  | .loadL l => 10 :: nat (ix l)
  | .storeL l => 11 :: nat (ix l)
  | .swapL l => 12 :: nat (ix l)
  | .tagL l => 13 :: nat (ix l)
  | .focusL l => 14 :: nat (ix l)

def instr (ix : Lay → Nat) : Instr → Bytes
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
  | .mem op args => 16 :: memOp ix op ++ list atom args
  | .cell init thunk => 17 :: atom init ++ atom thunk
  | .cellTail init thunk => 18 :: atom init ++ atom thunk
  | .cellL l init thunk => 20 :: laid ix l ++ atom init ++ atom thunk
  | .cellTailL l init thunk => 21 :: laid ix l ++ atom init ++ atom thunk
  | .lend uniq r thunk pre post =>
    19 :: (if uniq then 1 else 0) :: atom r ++ atom thunk ++ list atom pre ++ list atom post

def code (ix : Lay → Nat) (c : Code) : Bytes := list (instr ix) c

/-- The layouts a program's instructions are at, each once, in the order
they are first named: written once, before the functions, and named by
place, as one may be large and named by many. -/
def layTable (p : Program) : Array Lay × Std.HashMap Lay Nat := Id.run do
  let mut out : Array Lay := #[]
  let mut at_ : Std.HashMap Lay Nat := {}
  for c in p.fns.toList.map (·.code) ++ [p.main] do
    for i in c do
      let l? := match i with
        | .mem (.loadL l) _ | .mem (.storeL l) _ | .mem (.swapL l) _
        | .mem (.tagL l) _ | .mem (.focusL l) _ => some l
        | .cellL l _ _ | .cellTailL l _ _ => some l.lay
        | _ => none
      if let some l := l? then
        unless at_.contains l do
          at_ := at_.insert l out.size
          out := out.push l
  pure (out, at_)

def program (p : Program) : Bytes :=
  let (table, at_) := layTable p
  let ix := fun (l : Lay) => at_.getD l 0
  list lay table.toList ++ list (fun (f : Fn) => code ix f.code) p.fns.toList ++ code ix p.main
    ++ list pair p.drops ++ list (list nat) p.statics

def string (s : String) : Bytes := list (fun b => [b.toNat]) s.toUTF8.toList

/-- A bytecode file: the magic `GLBC`, a format version, the constructor names
used to print values, the functions' names (what `host_fn_name` gives),
and the program. -/
def file (ctorNames : List String) (p : Program) : Bytes :=
  [0x47, 0x4C, 0x42, 0x43, 9] ++ list string ctorNames ++ list string p.names.toList ++ program p

end Glorious.Bytecode.Encode
