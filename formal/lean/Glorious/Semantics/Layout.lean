import Glorious.Semantics.Storage

namespace Glorious.Semantics

def IntWidth.bits (target : Target) : IntWidth → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64 | .w128 => 128
  | .pointer => target.pointerBits

def scalarBits (target : Target) : ScalarType → Nat
  | .integer _ width => width.bits target
  | .floating .w32 => 32
  | .floating .w64 => 64
  | .character => 32

def alignUp (offset alignment : Nat) : Nat :=
  if alignment == 0 then offset else ((offset + alignment - 1) / alignment) * alignment

structure FieldLayout where
  type : Term
  offset : Nat
  size : Nat
  alignment : Nat
  deriving BEq, Repr

structure VariantLayout where
  declaration : DeclId
  fields : List FieldLayout
  size : Nat
  alignment : Nat
  deriving BEq, Repr

structure Layout where
  type : Term
  size : Nat
  alignment : Nat
  fields : List FieldLayout := []
  variants : List VariantLayout := []
  tagBits : Nat := 0
  payloadOffset : Nat := 0
  stride : Option Nat := none
  proofOnly : Bool := false
  cCompatible : Bool := false
  deriving BEq, Repr

def validateTarget (target : Target) : Check Unit := do
  require ([16, 32, 64, 128].contains target.pointerBits) .incompatibleABI "unsupported target pointer-width contract"
  require (target.maxObjectSize < 2 ^ target.pointerBits) .invalidLayout "target maximum object size exceeds usize"
  require (!target.layoutIdentity.isEmpty && !target.intrinsicManifest.isEmpty && !target.triple.isEmpty)
    .incompatibleABI "target descriptor omits an ABI identity"
  for (_, alignment) in target.scalarAlignments do
    require (alignment > 0 && Nat.land alignment (alignment - 1) == 0) .invalidLayout "scalar alignment is not a nonzero power of two"

def boundLayout (target : Target) (layout : Layout) : Check Layout := do
  require (layout.alignment > 0 && layout.size ≤ target.maxObjectSize) .invalidLayout "concrete layout exceeds target limits"
  require (layout.size % layout.alignment == 0) .invalidLayout "aggregate size is not padded to alignment"
  return layout

mutual
  def layoutOf (program : Program) (inference : Inference) : Nat → List Term → Term → Check Layout
    | 0, _, _ => reject .resourceLimit "concrete layout computation exhausted"
    | fuel + 1, active, original => do
      let type ← normalize program inference program.limits.normalization [] original
      require (!(active.contains type)) .invalidLayout "infinite inline owned layout"
      let target := program.target
      let pointerSize := target.pointerBits / 8
      let pointer : Layout := ⟨type, pointerSize, pointerSize, [], [], 0, 0, none, false, false⟩
      match type with
      | .unit | .bottom => return { type, size := 0, alignment := 1, cCompatible := false }
      | .scalar scalar =>
        let alignment ← getRequired (lookup scalar target.scalarAlignments) .invalidLayout "target omits this scalar alignment"
        boundLayout target { type, size := scalarBits target scalar / 8, alignment, cCompatible := scalar != .character }
      | .rawPointer .. => return { pointer with cCompatible := target.cEnabled }
      | .reference .. => return pointer
      | .label .. | .environment .. | .available .. =>
        return { type, size := 0, alignment := 1, proofOnly := true }
      | .bindings _ _ arguments =>
        layoutAggregate program inference fuel (type :: active) type arguments false
      | .tuple fields => layoutAggregate program inference fuel (type :: active) type fields false
      | .array element (.constant (.integer _ _ count)) =>
        require (count ≥ 0 && count.toNat < 2 ^ target.pointerBits) .invalidLayout "array length does not fit target usize"
        let element ← layoutOf program inference fuel (type :: active) element
        let stride := alignUp element.size element.alignment
        boundLayout target {
          type, size := stride * count.toNat, alignment := element.alignment,
          stride := some stride, cCompatible := false }
      | .nominal declaration arguments =>
        let data ← getRequired (program.dataType declaration) .unknownName "layout names an unknown nominal type"
        let subs ← bindArguments data.generics arguments
        let variants ← data.variants.mapM fun variant => do
          let fields ← variant.fields.mapM (fun field => substitute program.limits.normalization subs field.type)
          let layout ← layoutAggregate program inference fuel (type :: active) type fields
            (data.representation == .c || data.representation == .transparent)
          return (⟨variant.header.id, layout.fields, layout.size, layout.alignment⟩ : VariantLayout)
        match data.representation with
        | .transparent =>
          require (!data.isEnum && variants.length == 1) .invalidLayout "transparent representation requires one record variant"
          let variant ← getRequired variants.head? .invalidLayout "empty transparent representation"
          let nonzero := variant.fields.filter (fun field => field.size != 0)
          require (nonzero.length == 1) .invalidLayout "transparent representation requires exactly one nonzero field"
          let field ← getRequired nonzero.head? .invalidLayout "missing transparent representation field"
          return {
            type, size := field.size, alignment := field.alignment, fields := variant.fields,
            variants, cCompatible := target.cEnabled }
        | .integer signed width =>
          require (data.isEnum && variants.all (fun variant => variant.fields.isEmpty)) .invalidLayout "integer repr requires a fieldless enum"
          let bits := width.bits target
          let limit := if signed then 2 ^ (bits - 1) else 2 ^ bits
          require (variants.length ≤ limit) .invalidLayout "enum tags do not fit their representation"
          let scalar := ScalarType.integer signed width
          let alignment ← getRequired (lookup scalar target.scalarAlignments) .invalidLayout "missing enum-tag alignment"
          return { type, size := bits / 8, alignment, variants, tagBits := bits, cCompatible := target.cEnabled }
        | _ =>
          if !data.isEnum then
            let variant ← getRequired variants.head? .invalidLayout "record has no variant"
            require (variants.length == 1) .invalidLayout "record has several variants"
            return {
              type, size := variant.size, alignment := variant.alignment, fields := variant.fields,
              variants, cCompatible := data.representation == .c && target.cEnabled }
          require (data.representation != .c) .invalidLayout "C enum representation requires an explicitly fixed integer tag"
          let tagBits := if variants.length ≤ 256 then 8 else if variants.length ≤ 65536 then 16
            else if variants.length ≤ 4294967296 then 32 else 64
          let tagBytes := tagBits / 8
          let payloadAlignment := variants.foldl (fun alignment variant => max alignment variant.alignment) 1
          let alignment := max tagBytes payloadAlignment
          let payloadOffset := alignUp tagBytes payloadAlignment
          let payloadSize := variants.foldl (fun size variant => max size variant.size) 0
          boundLayout target {
            type, size := alignUp (payloadOffset + payloadSize) alignment,
            alignment, variants, tagBits, payloadOffset }
      | .callable declaration arguments =>
        let function ← getRequired (program.function declaration) .missingEvidence "callable layout lacks its declaration"
        let _ ← bindArguments function.signature.generics arguments
        -- Code identity plus a stable environment address. Capture storage is
        -- separately laid out from the same CoreFunction capture descriptors.
        return { type, size := pointerSize * 2, alignment := pointerSize }
      | .continuation .. => return { type, size := pointerSize * 2, alignment := pointerSize }
      | _ => reject .missingEvidence "runtime layout requires a closed, normalized source value type"

  def layoutAggregate (program : Program) (inference : Inference) (fuel : Nat)
      (active : List Term) (type : Term) (fields : List Term) (c : Bool) : Check Layout := do
    let (offset, alignment, layouts) ← fields.foldlM (init := (0, 1, [])) fun (offset, alignment, layouts) field => do
      let layout ← layoutOf program inference fuel active field
      require (!c || layout.cCompatible || layout.size == 0) .incompatibleABI "repr(C) field is not C-compatible"
      let cursor := alignUp offset layout.alignment
      require (cursor + layout.size ≤ program.target.maxObjectSize) .invalidLayout "record offset arithmetic exceeds target size"
      return (cursor + layout.size, max alignment layout.alignment,
        layouts ++ [(⟨field, cursor, layout.size, layout.alignment⟩ : FieldLayout)])
    boundLayout program.target {
      type, size := alignUp offset alignment, alignment,
      fields := layouts, cCompatible := c && program.target.cEnabled }
end

def checkForeignSignature (program : Program) (inference : Inference) (signature : Signature) : Check Unit := do
  require program.target.cEnabled .incompatibleABI "target does not advertise C interoperability"
  require signature.generics.isEmpty .incompatibleABI "C functions must be concrete and monomorphic"
  require (signature.effects == .row [] []) .incompatibleABI "Glorious effects may not cross an unadapted C boundary"
  for type in signature.output :: signature.arguments do
    if type != .unit && type != .bottom then
      let layout ← layoutOf program inference program.limits.layout [] type
      require layout.cCompatible .incompatibleABI "source type is not admitted by the C ABI"

def admitImports (program : Program) (inference : Inference) : Check Unit := do
  require (unique (program.imports.map (·.identity))) .duplicate "duplicate runtime import identity"
  for binding in program.imports do
    match binding.capability with
    | none => pure ()
    | some capability => require (program.grantedCapabilities.contains capability) .missingImport "runtime import requires an ungranted host capability"
    if binding.kind == .foreign then checkForeignSignature program inference binding.signature
    require (binding.signature.generics.isEmpty) .incompatibleABI "runtime leaf contract must be a concrete specialization"
  for function in program.functions do
    if function.body.isNone then
      let identity ← getRequired function.runtimeBinding .missingImport "ordinary bodyless function has no admitted runtime binding"
      let binding ← getRequired (program.imports.find? (fun binding => binding.identity == identity)) .missingImport "runtime declaration is not in the supplied import table"
      require (function.signature.arguments == binding.signature.arguments &&
        function.signature.output == binding.signature.output && function.signature.effects == binding.signature.effects &&
        function.signature.unsafeCall == binding.signature.unsafeCall && function.signature.abi == binding.signature.abi)
        .incompatibleABI "runtime declaration differs from its authenticated exact contract"
    if function.signature.abi == .c then checkForeignSignature program inference function.signature

end Glorious.Semantics
