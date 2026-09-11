import GloriousLanguage.Memory

/-! Finite machine leaves. Boolean flags here are u8 machine results; source
truth/result carriers remain ordinary nominal library data. A manifest binds
an exact primitive and signature, never a privileged library name. -/
namespace Glorious.Language.Execution

open Kernel Memory

def ScalarAt (world : World) (address : Address) (scalar : ScalarValue) : Prop :=
  ∃ value, world.Stores address value ∧ value.head = .scalar scalar ∧ value.Initialized

def PointerAt (world : World) (address : Address) (pointer : RawPointer) : Prop :=
  ∃ value, world.Stores address value ∧ value.head = .pointer pointer ∧ value.Initialized

inductive ScalarValues (world : World) : List Address → List ScalarValue → Prop where
  | nil : ScalarValues world [] []
  | cons {address addresses scalar scalars} : ScalarAt world address scalar → ScalarValues world addresses scalars →
      ScalarValues world (address :: addresses) (scalar :: scalars)

def IntegerArity (operation : IntegerOperation) : Nat := if operation = .negate then 1 else 2
def FloatArity : FloatOperation → Nat
  | .negate | .absolute | .squareRoot => 1
  | .fusedMultiplyAdd => 3
  | _ => 2

inductive IntegerCalculation (target : TargetProfile) (signed : Bool) (width : Width) :
    IntegerOperation → Overflow → List Int → Except Fatal Int → Prop where
  | binary {op overflow a b raw result} : IntegerArity op = 2 →
      IntegerRange target signed width a → IntegerRange target signed width b →
      (op = .shiftLeft ∨ op = .shiftRight → 0 ≤ b ∧ b < width.bits target) →
      integerOperation op a b = some raw → IntegerResult target signed width overflow raw result →
      IntegerCalculation target signed width op overflow [a,b] result
  | unary {overflow a result} : IntegerRange target signed width a →
      IntegerResult target signed width overflow (-a) result →
      IntegerCalculation target signed width .negate overflow [a] result
  | zeroDivisor {op overflow a} : (op = .divide ∨ op = .remainder) →
      IntegerRange target signed width a → IntegerCalculation target signed width op overflow [a,0] (.error .arithmetic)
  | invalidShift {op overflow a b} : (op = .shiftLeft ∨ op = .shiftRight) →
      IntegerRange target signed width a → IntegerRange target signed width b →
      (b < 0 ∨ Int.ofNat (width.bits target) ≤ b) →
      IntegerCalculation target signed width op overflow [a,b] (.error .arithmetic)

def FloatEqual (width : FloatWidth) (a b : Nat) : Prop :=
  (∃ sa sb ma mb ea eb,
    decodeFloat width a = some (.finite sa ma ea) ∧ decodeFloat width b = some (.finite sb mb eb) ∧
    (binaryFraction sa ma ea).Equal (binaryFraction sb mb eb)) ∨
  ∃ sign, decodeFloat width a = some (.infinity sign) ∧ decodeFloat width b = some (.infinity sign)

def FloatLess (width : FloatWidth) (a b : Nat) : Prop :=
  (∃ sa sb ma mb ea eb, decodeFloat width a = some (.finite sa ma ea) ∧ decodeFloat width b = some (.finite sb mb eb) ∧
    (binaryFraction sa ma ea).Le (binaryFraction sb mb eb) ∧ ¬ (binaryFraction sb mb eb).Le (binaryFraction sa ma ea)) ∨
  (decodeFloat width a = some (.infinity true) ∧ (∃ value, decodeFloat width b = some value ∧ value ≠ .nan ∧ value ≠ .infinity true)) ∨
  (decodeFloat width b = some (.infinity false) ∧ (∃ value, decodeFloat width a = some value ∧ value ≠ .nan ∧ value ≠ .infinity false))

def ScalarEqual : ScalarValue → ScalarValue → Prop
  | .integer sa wa a, .integer sb wb b => sa = sb ∧ wa = wb ∧ a = b
  | .character a, .character b => a = b
  | .floating wa a, .floating wb b => wa = wb ∧ FloatEqual wa a b
  | _, _ => False

def ScalarLess : ScalarValue → ScalarValue → Prop
  | .integer sa wa a, .integer sb wb b => sa = sb ∧ wa = wb ∧ a < b
  | .character a, .character b => a < b
  | .floating wa a, .floating wb b => wa = wb ∧ FloatLess wa a b
  | _, _ => False

inductive ScalarConversion (target : TargetProfile) : ScalarValue → Scalar → Except Fatal ScalarValue → Prop where
  | integer {sourceSign sourceWidth value sign width} : IntegerRange target sourceSign sourceWidth value →
      IntegerRange target sign width value →
      ScalarConversion target (.integer sourceSign sourceWidth value) (.integer sign width) (.ok (.integer sign width value))
  | integerOverflow {sourceSign sourceWidth value sign width} : IntegerRange target sourceSign sourceWidth value →
      ¬ IntegerRange target sign width value →
      ScalarConversion target (.integer sourceSign sourceWidth value) (.integer sign width) (.error .arithmetic)
  | integerFloat {sign width value float result} : IntegerRange target sign width value → Rounded float ⟨value,1⟩ false result →
      ScalarConversion target (.integer sign width value) (.floating float) (.ok (.floating float result))
  | floatInteger {width bits sign significand exponent destinationSign destinationWidth fraction value} :
      decodeFloat width bits = some (.finite sign significand exponent) → fraction = binaryFraction sign significand exponent →
      value = fraction.numerator.tdiv fraction.denominator → IntegerRange target destinationSign destinationWidth value →
      ScalarConversion target (.floating width bits) (.integer destinationSign destinationWidth)
        (.ok (.integer destinationSign destinationWidth value))
  | floatIntegerInvalid {width bits sign destinationWidth} :
      ((∃ negative, decodeFloat width bits = some (.infinity negative)) ∨ decodeFloat width bits = some .nan ∨
        ∃ negative m e fraction, decodeFloat width bits = some (.finite negative m e) ∧
          fraction = binaryFraction negative m e ∧ ¬ IntegerRange target sign destinationWidth (fraction.numerator.tdiv fraction.denominator)) →
      ScalarConversion target (.floating width bits) (.integer sign destinationWidth) (.error .arithmetic)
  | float {sourceWidth bits sign m e destinationWidth result} : decodeFloat sourceWidth bits = some (.finite sign m e) →
      Rounded destinationWidth (binaryFraction sign m e) sign result →
      ScalarConversion target (.floating sourceWidth bits) (.floating destinationWidth) (.ok (.floating destinationWidth result))
  | floatInfinity {sourceWidth bits sign destinationWidth result} : decodeFloat sourceWidth bits = some (.infinity sign) →
      decodeFloat destinationWidth result = some (.infinity sign) →
      ScalarConversion target (.floating sourceWidth bits) (.floating destinationWidth) (.ok (.floating destinationWidth result))
  | floatNaN {sourceWidth bits destinationWidth} : decodeFloat sourceWidth bits = some .nan →
      ScalarConversion target (.floating sourceWidth bits) (.floating destinationWidth) (.ok (.floating destinationWidth (canonicalNaN destinationWidth)))
  | character {sign width value} : 0 ≤ value → Source.UnicodeScalar value.toNat → IntegerRange target sign width value →
      ScalarConversion target (.integer sign width value) .character (.ok (.character value.toNat))
  | characterInvalid {sign width value} : IntegerRange target sign width value →
      (value < 0 ∨ ¬ Source.UnicodeScalar value.toNat) →
      ScalarConversion target (.integer sign width value) .character (.error .invalidValue)
  | characterInteger {value sign width} : Source.UnicodeScalar value → IntegerRange target sign width value →
      ScalarConversion target (.character value) (.integer sign width) (.ok (.integer sign width value))

inductive PrimitiveCalculation (target : TargetProfile) : Primitive → List Term → List ScalarValue → Except Fatal ScalarValue → Prop where
  | integer {op sign width overflow integers result} :
      IntegerCalculation target sign width op overflow integers (.ok result) →
      PrimitiveCalculation target (.integer op sign width overflow) [] (integers.map (.integer sign width)) (.ok (.integer sign width result))
  | integerFault {op sign width overflow integers reason} :
      IntegerCalculation target sign width op overflow integers (.error reason) →
      PrimitiveCalculation target (.integer op sign width overflow) [] (integers.map (.integer sign width)) (.error reason)
  | floating {op width inputs result} : inputs.length = FloatArity op → FloatCalculation width op inputs result →
      PrimitiveCalculation target (.floating op width) [] (inputs.map (.floating width)) (.ok (.floating width result))
  | equal {a b flag} : a.type = b.type → a.Valid target → b.Valid target →
      ((flag = 1 ∧ ScalarEqual a b) ∨ (flag = 0 ∧ ¬ ScalarEqual a b)) →
      PrimitiveCalculation target .scalarEqual [] [a,b] (.ok (.integer false (.fixed 8) flag))
  | less {a b flag} : a.type = b.type → a.Valid target → b.Valid target →
      ((flag = 1 ∧ ScalarLess a b) ∨ (flag = 0 ∧ ¬ ScalarLess a b)) →
      PrimitiveCalculation target .scalarLess [] [a,b] (.ok (.integer false (.fixed 8) flag))
  | convert {source destination result} : ScalarConversion target source destination result →
      PrimitiveCalculation target .scalarConvert [.scalar destination] [source] result

def StoresScalar (program : Kernel.Program) (before : World) (destination : Address) (scalar : ScalarValue) (after : World) : Prop :=
  scalar.Valid program.declarations.input.target ∧ DestinationType before destination (.scalar scalar.type) ∧
  NewValue program.declarations before destination (.scalar scalar.type) (.scalar scalar) [] after

def StoresUnit (program : Kernel.Program) (before : World) (destination : Address) (after : World) : Prop :=
  DestinationType before destination .unit ∧ NewValue program.declarations before destination .unit .unit [] after

def StoresPointer (program : Kernel.Program) (before : World) (destination : Address)
    (mode : Mutability) (type : Term) (pointer : RawPointer) (after : World) : Prop :=
  DestinationType before destination (.rawPointer mode type) ∧
  NewValue program.declarations before destination (.rawPointer mode type) (.pointer pointer) [] after

inductive PrimitiveStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | scalar {before context destination binding arguments operands next primitive values result after} :
      before.task = .primitive context destination binding arguments operands next → binding.primitive = some primitive →
      ScalarValues before.world operands values → PrimitiveCalculation program.declarations.input.target primitive arguments values (.ok result) →
      StoresScalar program before.world destination result after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | scalarFault {before context destination binding arguments operands next primitive values reason} :
      before.task = .primitive context destination binding arguments operands next → binding.primitive = some primitive →
      ScalarValues before.world operands values → PrimitiveCalculation program.declarations.input.target primitive arguments values (.error reason) →
      PrimitiveStep program before (some (.fatal reason)) { before with task := .fatal reason }
  | allocate {before context destination binding element countAddress next count domain base pointer allocated after} :
      before.task = .primitive context destination binding [element] [countAddress] next → binding.primitive = some .allocate →
      binding.domain = some domain → ScalarAt before.world countAddress (.integer false .pointer count) → 0 ≤ count →
      AllocatesBuffer program.declarations before.world domain element count.toNat base pointer allocated →
      StoresPointer program allocated destination .unique element pointer after →
      PrimitiveStep program before (some (.allocate ⟨before.world.nextRoot,0,[]⟩))
        { before with world := after, task := .run context next }
  | release {before context destination binding pointerAddress next pointer domain released after} :
      before.task = .primitive context destination binding [] [pointerAddress] next → binding.primitive = some .release →
      binding.domain = some domain → PointerAt before.world pointerAddress pointer →
      ReleasesBuffer program.declarations before.world pointer domain released → StoresUnit program released destination after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | reallocate {before context destination binding element pointerAddress countAddress next old count domain base pointer allocated after} :
      before.task = .primitive context destination binding [element] [pointerAddress,countAddress] next → binding.primitive = some .reallocate →
      binding.domain = some domain → PointerAt before.world pointerAddress old →
      ScalarAt before.world countAddress (.integer false .pointer count) → 0 ≤ count →
      ReallocatesBuffer program.declarations before.world old domain element count.toNat base pointer allocated →
      StoresPointer program allocated destination .unique element pointer after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | rawRead {before context destination binding type pointerAddress next pointer after} :
      before.task = .primitive context destination binding [type] [pointerAddress] next → binding.primitive = some .rawRead →
      PointerAt before.world pointerAddress pointer → RawRead program.declarations before.world pointer type false destination after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | rawCopy {before context destination binding type pointerAddress next pointer after} :
      before.task = .primitive context destination binding [type] [pointerAddress] next → binding.primitive = some .rawCopy →
      PointerAt before.world pointerAddress pointer → RawRead program.declarations before.world pointer type true destination after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | rawWrite {before context destination binding type source pointerAddress next pointer written after} :
      before.task = .primitive context destination binding [type] [source,pointerAddress] next → binding.primitive = some .rawWrite →
      PointerAt before.world pointerAddress pointer → RawWrite program.declarations before.world source pointer type written →
      StoresUnit program written destination after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | rawBorrow {before context destination binding type pointerAddress next pointer mode after} :
      before.task = .primitive context destination binding [.reference mode (.rigid context.region .region 0) type] [pointerAddress] next →
      binding.primitive = some .rawBorrow → PointerAt before.world pointerAddress pointer →
      RawBorrow program.declarations before.world pointer type mode context.region destination after →
      PrimitiveStep program before (some (.borrow ⟨pointer.allocation.getD 0,pointer.generation,[]⟩ before.world.nextLoan))
        { before with world := after, task := .run context next }
  | pointerOffset {before context destination binding type pointerAddress offsetAddress next pointer offset result after mode} :
      before.task = .primitive context destination binding [type] [pointerAddress,offsetAddress] next → binding.primitive = some .pointerOffset →
      PointerAt before.world pointerAddress pointer → ScalarAt before.world offsetAddress (.integer true .pointer offset) →
      PointerOffset program.declarations before.world pointer offset result → StoresPointer program before.world destination mode type result after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | pointerAddress {before context destination binding pointerAddress next pointer after} :
      before.task = .primitive context destination binding [] [pointerAddress] next → binding.primitive = some .pointerAddress →
      PointerAt before.world pointerAddress pointer →
      StoresScalar program before.world destination (.integer false .pointer pointer.address) after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | pointerWithAddress {before context destination binding type pointerAddress integerAddress next pointer integer result after mode} :
      before.task = .primitive context destination binding [type] [pointerAddress,integerAddress] next → binding.primitive = some .pointerWithAddress →
      PointerAt before.world pointerAddress pointer → ScalarAt before.world integerAddress (.integer false .pointer integer) →
      0 ≤ integer → WithAddress program.declarations before.world pointer integer.toNat result →
      StoresPointer program before.world destination mode type result after →
      PrimitiveStep program before none { before with world := after, task := .run context next }
  | layout {before context destination binding type next layout size alignment allocated after} :
      before.task = .primitive context destination binding [type] [] next → binding.primitive = some .layout →
      LayoutOf program.declarations context.static type layout →
      ConstantValue program.declarations context.static before.world.nextOwner
        (.constantTuple [.constant (.integer false .pointer layout.size),.constant (.integer false .pointer layout.alignment)])
        allocated size → before.world.write destination (some size) = some after → alignment = allocated →
      PrimitiveStep program before none { before with world := { after with nextOwner := alignment }, task := .run context next }
  | abort {before context destination binding arguments operands next} :
      before.task = .primitive context destination binding arguments operands next → binding.primitive = some .abort →
      PrimitiveStep program before (some (.fatal .abort)) { before with task := .fatal .abort }

end Glorious.Language.Execution
