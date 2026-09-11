import Glorious.Semantics.Scalar

/-! Runtime leaves operate on the same owners, loans and allocation identities
as ordinary Core. A raw address does not create a reference loan or authorize
copying a resident. Missing bytes/provenance remain missing evidence. -/
namespace Glorious.Semantics

inductive MemoryOperation where
  | allocate | resize | release | offset | distance | cast | expose | fromAddress
  | read | copyRead | write | replace | copyBytes | moveBytes | fillBytes
  | addressOf | sizeOf | alignOf | abort
  deriving BEq, Repr

def memoryOperation (name : String) : Option MemoryOperation :=
  lookup name [
    ("RawAlloc", .allocate), ("RawRealloc", .resize), ("RawDealloc", .release),
    ("RawOffset", .offset), ("RawDistance", .distance), ("RawCast", .cast),
    ("RawExposeAddress", .expose), ("RawFromAddress", .fromAddress),
    ("RawRead", .read), ("RawCopyRead", .copyRead), ("RawWrite", .write),
    ("RawReplace", .replace), ("RawCopy", .copyBytes), ("RawMove", .moveBytes),
    ("RawFill", .fillBytes), ("RawAddressOf", .addressOf),
    ("SizeOf", .sizeOf), ("AlignOf", .alignOf), ("Abort", .abort)]

def integerValue (value : Value) : Check Int :=
  match value.head with
  | .scalar (.integer _ _ value) => return value
  | _ => reject .missingEvidence "machine integer operand is not known"

def naturalValue (value : Value) : Check Nat := do
  let value ← integerValue value
  require (value ≥ 0) .invalidPointer "memory extent is negative"
  return value.toNat

def pointerValue (value : Value) : Check Pointer :=
  match value.head with
  | .pointer pointer => return pointer
  | _ => reject .missingEvidence "memory address has no represented provenance"

def memoryArgument (values : List Value) (index : Nat) : Check Value :=
  getRequired values[index]? .incompatibleABI "missing machine argument"

def allocationFor (world : World) (pointer : Pointer) : Check Allocation := do
  let identity ← getRequired pointer.allocation .invalidPointer "pointer is not a runtime allocation"
  let allocation ← getRequired (world.allocations.find? (fun a => a.identity == identity && a.alive))
    .invalidPointer "allocation identity is absent or has been released"
  require (pointer.provenance == some allocation.provenance) .invalidPointer "raw address has no matching allocation provenance"
  return allocation

def memoryRange (program : Program) (pointer : Pointer) (size alignment : Nat)
    (write : Bool) : WorldM Allocation := do
  let allocation ← allocationFor (← get) pointer
  require (!write || pointer.mutable) .invalidPointer "write through an immutable raw pointer"
  require (pointer.offset ≥ 0 && pointer.offset.toNat + size ≤ allocation.size)
    .invalidPointer "raw access leaves its live allocation"
  require (alignment > 0 && allocation.alignment % alignment == 0 && pointer.offset.toNat % alignment == 0)
    .invalidPointer "raw access violates alignment"
  require (size ≤ program.target.maxObjectSize) .invalidLayout "raw access exceeds target object bound"
  return allocation

def updateAllocation (allocation : Allocation) : WorldM Unit :=
  modify fun world => { world with allocations := world.allocations.map
    (fun current => if current.identity == allocation.identity then allocation else current) }

def byteInitialized (allocation : Allocation) (offset : Nat) : Bool :=
  allocation.initialized.any (fun (start, stop) => start ≤ offset && offset < stop)

def rawResident (program : Program) (inference : Inference) (pointer : Pointer)
    (type : Term) (copy : Bool) : WorldM Value := do
  let layout ← layoutOf program inference program.limits.layout [] type
  if let some address := pointer.source then
    require (pointer.offset == 0) .missingEvidence "derived source address requires a checked subobject layout"
    let world ← get
    let value ← lookupAddress program world address >>= fun value =>
      getRequired value .uninitialized "raw read reaches an uninitialized source owner"
    require (value.type == type) .invalidPointer "raw source read uses a different resident type"
    let located : Located := ⟨address, type, none⟩
    checkAccess program world located (if copy then .read else .move)
    if copy then copyValue program value else
      updateAddress program address none
      return value
  else
    let allocation ← memoryRange program pointer layout.size layout.alignment (!copy)
    let value ← getRequired (lookup pointer.offset.toNat allocation.residents)
      .uninitialized "raw read has no initialized typed resident"
    require (value.type == type) .invalidPointer "raw read type differs from its initialized resident"
    if copy then copyValue program value else
      updateAllocation { allocation with residents := allocation.residents.filter (fun cell => cell.1 != pointer.offset.toNat) }
      return value

def rawStore (program : Program) (inference : Inference) (pointer : Pointer)
    (value : Value) (replace : Bool) : WorldM (Option Value) := do
  let layout ← layoutOf program inference program.limits.layout [] value.type
  require pointer.mutable .invalidPointer "raw store lacks mutation authority"
  if let some address := pointer.source then
    require (pointer.offset == 0) .missingEvidence "derived source store needs a checked subobject layout"
    let world ← get
    let prior ← lookupAddress program world address
    checkAccess program world ⟨address, value.type, none⟩ .write
    require (replace || prior.isNone) .illegalDiscard "raw initialization would overwrite an undisposed owner"
    require (!replace || prior.isSome) .uninitialized "raw replacement requires an initialized owner"
    updateAddress program address (some value)
    return prior
  else
    let allocation ← memoryRange program pointer layout.size layout.alignment true
    let prior := lookup pointer.offset.toNat allocation.residents
    require (replace || prior.isNone) .illegalDiscard "raw initialization would overwrite an undisposed owner"
    require (!replace || prior.isSome) .uninitialized "raw replacement requires an initialized owner"
    for (offset, resident) in allocation.residents do
      let residentLayout ← layoutOf program inference program.limits.layout [] resident.type
      require (offset == pointer.offset.toNat || offset + residentLayout.size ≤ pointer.offset.toNat ||
        pointer.offset.toNat + layout.size ≤ offset) .invalidPointer "raw store overlaps another initialized resident"
    updateAllocation { allocation with residents := put pointer.offset.toNat value allocation.residents,
      initialized := (pointer.offset.toNat, pointer.offset.toNat + layout.size) :: allocation.initialized }
    return prior

def executeMemory (program : Program) (inference : Inference) (binding : RuntimeImport)
    (operation : MemoryOperation) (values : List Value) : WorldM (Option Value) := do
  let arg := memoryArgument values
  let scalar (value : Int) := createValue program inference binding.signature.output
    (.scalar (.integer false .pointer value))
  let unit := createValue program inference .unit .unit
  let pointerResult (pointer : Pointer) := createValue program inference binding.signature.output (.pointer pointer)
  match operation with
  | .abort => return none
  | .allocate =>
    let size ← arg 0 >>= naturalValue
    let alignment ← arg 1 >>= naturalValue
    require (alignment > 0 && Nat.land alignment (alignment - 1) == 0 && size ≤ program.target.maxObjectSize)
      .invalidLayout "allocation has invalid extent or alignment"
    let domain ← getRequired binding.allocationDomain .missingImport "allocator lacks a bound allocation domain"
    let world ← get
    let allocation : Allocation := ⟨world.nextAllocation, world.nextAllocation, domain, size, alignment, true, [], [], []⟩
    set { world with nextAllocation := world.nextAllocation + 1, allocations := world.allocations ++ [allocation] }
    return some (← pointerResult ⟨some allocation.identity, 0, some allocation.provenance, true, none⟩)
  | .resize | .release =>
    let pointer ← arg 0 >>= pointerValue
    let allocation ← allocationFor (← get) pointer
    require (pointer.offset == 0 && binding.allocationDomain == some allocation.domain)
      .invalidPointer "allocation release/resize uses a different base or allocator domain"
    if operation == .release then
      require allocation.residents.isEmpty .illegalDiscard "allocation release retains initialized logical owners"
      updateAllocation { allocation with alive := false, initialized := [], byteValues := [] }
      return some (← unit)
    else
      let size ← arg 1 >>= naturalValue
      require (size ≤ program.target.maxObjectSize) .invalidLayout "resized allocation exceeds target limits"
      for (offset, value) in allocation.residents do
        let layout ← layoutOf program inference program.limits.layout [] value.type
        require (offset + layout.size ≤ size) .illegalDiscard "allocation shrink truncates a live resident"
      updateAllocation { allocation with size, byteValues := allocation.byteValues.filter (fun byte => byte.1 < size),
        initialized := allocation.initialized.map (fun (a, b) => (min a size, min b size)) }
      return some (← pointerResult pointer)
  | .offset =>
    let pointer ← arg 0 >>= pointerValue
    let offset ← arg 1 >>= integerValue
    let pointer := { pointer with offset := pointer.offset + offset }
    if pointer.allocation.isSome then
      let allocation ← allocationFor (← get) pointer
      require (pointer.offset ≥ 0 && pointer.offset.toNat ≤ allocation.size) .invalidPointer "offset leaves allocation including its one-past end"
    return some (← pointerResult pointer)
  | .distance =>
    let a ← arg 0 >>= pointerValue
    let b ← arg 1 >>= pointerValue
    require (a.allocation.isSome && a.allocation == b.allocation && a.provenance == b.provenance)
      .invalidPointer "pointer distance requires the same live allocation"
    let _ ← allocationFor (← get) a
    return some (← scalar (a.offset - b.offset))
  | .cast => return some (← pointerResult (← arg 0 >>= pointerValue))
  | .fromAddress =>
    let bits ← arg 0 >>= integerValue
    return some (← pointerResult ⟨none, bits, none, true, none⟩)
  | .expose =>
    let pointer ← arg 0 >>= pointerValue
    require (pointer.allocation.isNone && pointer.source.isNone) .missingEvidence "allocation address exposure requires a concrete runtime address assignment"
    return some (← scalar pointer.offset)
  | .addressOf =>
    let value ← arg 0
    let loan ← match value.head with
      | .reference identity => getRequired ((← get).loans.find? (fun l => l.identity == identity && l.live))
          .invalidPointer "raw address construction sees an ended reference"
      | _ => reject .typeMismatch "raw address construction requires a reference"
    return some (← pointerResult ⟨none, 0, none, loan.mode == .unique, some loan.origin⟩)
  | .read | .copyRead =>
    let pointer ← arg 0 >>= pointerValue
    return some (← rawResident program inference pointer binding.signature.output (operation == .copyRead))
  | .write | .replace =>
    let pointer ← arg 0 >>= pointerValue
    let value ← arg 1
    let old ← rawStore program inference pointer value (operation == .replace)
    if operation == .replace then return old else return some (← unit)
  | .sizeOf | .alignOf =>
    let type ← getRequired binding.signature.arguments.head? .incompatibleABI "layout query lacks a type witness"
    let layout ← layoutOf program inference program.limits.layout [] type
    return some (← scalar (if operation == .sizeOf then layout.size else layout.alignment))
  | .copyBytes | .moveBytes | .fillBytes =>
    let destination ← arg 0 >>= pointerValue
    let size ← arg 2 >>= naturalValue
    let target ← memoryRange program destination size 1 true
    require target.residents.isEmpty .missingEvidence "byte mutation of typed residents requires the checked representation transition"
    let bytes ← if operation == .fillBytes then do
        let byte ← arg 1 >>= naturalValue
        require (byte < 256) .invalidScalar "byte fill value does not fit u8"
        pure (List.replicate size (UInt8.ofNat byte))
      else do
        let source ← arg 1 >>= pointerValue
        let allocation ← memoryRange program source size 1 false
        require allocation.residents.isEmpty .missingEvidence "byte copying typed owners requires a typed relocation contract"
        if operation == .copyBytes then
          require (source.allocation != destination.allocation ||
            source.offset + Int.ofNat size ≤ destination.offset || destination.offset + Int.ofNat size ≤ source.offset)
            .invalidPointer "non-overlapping byte copy overlaps"
        (List.range size).mapM fun index => do
          require (byteInitialized allocation (source.offset.toNat + index)) .uninitialized "bulk read reaches uninitialized bytes"
          getRequired (lookup (source.offset.toNat + index) allocation.byteValues) .missingEvidence "bulk read byte contents are unknown"
    let stored := bytes.zipIdx |>.map fun (byte, index) => (destination.offset.toNat + index, byte)
    updateAllocation { target with byteValues := stored.foldl (fun table (offset, byte) => put offset byte table) target.byteValues,
      initialized := (destination.offset.toNat, destination.offset.toNat + size) :: target.initialized }
    return some (← unit)

def scalarOperationName (name : String) : Option (ScalarType × String) := do
  let prefix ← ["Usize", "Isize", "U128", "I128", "U64", "I64", "U32", "I32", "U16", "I16", "U8", "I8", "F32", "F64", "Char"].find? name.startsWith
  let scalar ← lookup prefix [
    ("Usize", .integer false .pointer), ("Isize", .integer true .pointer),
    ("U128", .integer false .w128), ("I128", .integer true .w128),
    ("U64", .integer false .w64), ("I64", .integer true .w64),
    ("U32", .integer false .w32), ("I32", .integer true .w32),
    ("U16", .integer false .w16), ("I16", .integer true .w16),
    ("U8", .integer false .w8), ("I8", .integer true .w8),
    ("F32", .floating .w32), ("F64", .floating .w64), ("Char", .character)]
  return (scalar, String.ofList (name.toList.drop prefix.length))

def executeScalar (program : Program) (inference : Inference) (binding : RuntimeImport)
    (name : String) (values : List Value) : WorldM Value := do
  let (scalar, operation) ← getRequired (scalarOperationName name) .missingImport "unknown scalar primitive identity"
  let left ← memoryArgument values 0
  let right := values[1]?.getD left
  let result ← match scalar, left.head, right.head with
    | .integer signed width, .scalar (.integer _ _ a), .scalar (.integer _ _ b) =>
      let spelling := operation.replace "Wrapping" ""
      let op ← getRequired (lookup spelling [
        ("Add", IntegerOperation.add), ("Sub", .sub), ("Mul", .mul), ("Div", .div), ("Rem", .rem),
        ("Neg", .neg), ("BitAnd", .bitAnd), ("BitOr", .bitOr), ("BitXor", .bitXor), ("BitNot", .bitNot),
        ("Shl", .shl), ("Shr", .shr), ("Eq", .eq), ("Ne", .ne), ("Lt", .lt), ("Le", .le), ("Gt", .gt), ("Ge", .ge)])
        .missingImport "unrecognized integer operation"
      integerOperation program.target op (if operation.startsWith "Wrapping" then .wrapping else .checked) signed width a b
    | .floating width, .scalar (.floating _ a), .scalar (.floating _ b) =>
      let op ← getRequired (lookup operation [("Add", FloatOperation.add), ("Sub", .sub), ("Mul", .mul),
        ("Div", .div), ("Rem", .rem), ("Neg", .neg), ("Eq", .eq), ("Ne", .ne), ("Lt", .lt), ("Le", .le), ("Gt", .gt), ("Ge", .ge)])
        .missingImport "unrecognized floating operation"
      floatOperation program.limits.execution width op a b
    | _, .symbolic _, _ | _, _, .symbolic _ =>
      return ← createValue program inference binding.signature.output (.symbolic (← get).nextOwner)
    | _, _, _ => reject .incompatibleABI "scalar primitive operands differ from its bound format"
  require (scalarValueType result == binding.signature.output) .incompatibleABI "scalar result differs from its bound signature"
  createValue program inference binding.signature.output (.scalar result)

def executeLeaf (program : Program) (inference : Inference) (binding : RuntimeImport)
    (values : List Value) : WorldM (Option Value) := do
  require (values.map Value.type == binding.signature.arguments) .incompatibleABI "runtime operands differ from the admitted concrete contract"
  if let some name := binding.primitive then
    if let some memory := memoryOperation name then executeMemory program inference binding memory values
    else return some (← executeScalar program inference binding name values)
  else
    require ([LeafKind.host, .foreign, .staticData].contains binding.kind) .missingImport "intrinsic leaf has no primitive identity"
    require (!binding.retainedCallback) .unsupportedContract "retained host callbacks require a persistent invocation/lease contract"
    sealValues program values
    return some (← createValue program inference binding.signature.output (.symbolic (← get).nextOwner))

end Glorious.Semantics
