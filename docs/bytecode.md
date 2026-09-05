# Grandiose Bytecode Generation 1

The [unsafe/native-ABI amendment](unsafe-memory-and-native-abi.md) defines future
versioned raw-memory, guest-safety, and shared-layout requirements. It does not
reassign or weaken the existing G1 encodings and verifier contracts below.

The selected extension must execute concrete source-library specializations,
including unsafe memory operations, as bytecode over host-compatible storage.
Unsafe-enabled execution is not an in-process memory sandbox. Current distribution
ships source for local compilation; independent admission of untrusted new-format
bytecode is deferred. Existing G1 checks below remain intact. Shared native calls need
target/layout and call/ownership contracts plus actual VM/host tests, not a
Glorious LLVM backend. LLVM is deferred until after verified self-hosting.
This decision allocates no opcode, feature bit, profile flag, or CLI switch.
In particular, it does not reinterpret existing fixed-width `usize`/`isize`
values or portable container fields as native pointer representations.

The separate Stage0 authoring format now has schema 94 raw-memory execution for
locally compiled source; see its [implementation state](../compiler/spec/unsafe-memory-progress.md#u3-initial-locally-compiled-raw-memory-execution).
That extension is not a G1 opcode assignment or independent G1 safety certificate.

Status: normative. Keywords **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are to
be interpreted as requirements. Generation 1 is abbreviated G1.

## 1. Compatibility contract

A valid released artifact remains valid and has the same observable behavior on
every newer conforming VM, except for explicitly external host state. Existing
section, feature, type, primitive, opcode, flag, and host-symbol identifiers are
never reassigned. Their accepted encodings and semantics are never narrowed or
changed. New encodings are additive.

A VM MUST reject, before execution, an artifact with an unknown required feature,
unknown critical section, unsupported format major, noncanonical encoding, or
failed verification. Rejection is a structured compatibility/verification error,
not a host panic. Unknown noncritical sections MUST be skipped.

An artifact declares the minimum features it uses, not every feature understood
by its producer. G1 writers MUST set feature bit 0 and exactly the other G1 bits
whose facilities appear. A newer VM MUST continue decoding major version 1.
If a future incompatible container needs major version 2, that VM MUST also retain
its major-1 decoder. Minor version is informational and does not alter semantics.

## 2. Scalar conventions

- Integers in the container are unsigned little-endian unless stated otherwise.
- `u8`, `u16`, `u32`, and `u64` have their usual fixed widths.
- `NONE32` is `0xffffffff`; `NONE64` is `0xffffffffffffffff`.
- Booleans in metadata are `u8` values 0 and 1 only.
- All offsets are absolute file-byte offsets unless a section says otherwise.
- All table indices are zero-based `u32` values.
- All reserved bytes/bits MUST be zero.
- Text is valid shortest-form UTF-8 and MUST NOT contain an encoded surrogate.
- `usize`/`isize` bytecode values are always 64-bit, independent of the host.
- IEEE floating constants are stored as their raw little-endian bit patterns.
  All NaNs are canonicalized to quiet NaN `0x7fc00000` or
  `0x7ff8000000000000` by a canonical writer.

## 3. File container

### 3.1 Header

Every file begins with this 64-byte header:

| Offset | Size | Field | G1 value/meaning |
|---:|---:|---|---|
| 0 | 8 | magic | bytes `47 52 42 43 0d 0a 1a 0a` (`GRBC` + sentinel) |
| 8 | 2 | format_major | `1` |
| 10 | 2 | format_minor | `0` for this document |
| 12 | 4 | header_size | `64` |
| 16 | 4 | flags | header flags below |
| 20 | 4 | section_count | number of directory records |
| 24 | 4 | directory_entry_size | `32` |
| 28 | 4 | entry_function | function index or `NONE32` for a library |
| 32 | 8 | required_features_lo | feature IDs 0 through 63 |
| 40 | 8 | required_features_hi | feature IDs 64 through 127 |
| 48 | 8 | directory_offset | first directory record; G1 canonical value `64` |
| 56 | 8 | file_size | exact byte length of the file |

Header flag `0x00000001` means executable and requires `entry_function` not to be
`NONE32`. All other G1 header flags are reserved. A library MUST use flags 0 and
`entry_function = NONE32`. The executable entry MUST be a direct function with
signature `() -> Unit`, an empty outward protocol list, and no captures. Normal
return gives process status 0; all other status categories are assigned by the
supervisor.

Feature IDs are permanent:

| Bit | Name | Required when |
|---:|---|---|
| 0 | `CORE_G1` | always |
| 1 | `REFERENCES_G1` | any reference type or borrow instruction occurs |
| 2 | `LABELS_G1` | any label instruction occurs |
| 3 | `HANDLERS_G1` | protocol, handler, perform, or one-shot resumption occurs |
| 4 | `MULTISHOT_G1` | a resumption has an upper bound greater than one |
| 5 | `HOST_ABI_G1` | the import table is nonempty |
| 6 | `ARRAY_RESERVE_G1` | `array.capacity` or `array.reserve` occurs |
| 7 | `ARRAY_FINISH_DRAINED_G1` | `array.finish_drained` occurs |
| 8 | `BYTES_UTF8_VALID_UP_TO_G1` | `bytes.utf8_valid_up_to` occurs |

Bits 9 through 127 are unassigned and therefore unknown. Features beyond 127
MUST be introduced by a new critical `FEATURES` section; section ID 14 is
reserved for that future definition. G1 artifacts MUST NOT contain it.

### 3.2 Section directory

The directory immediately follows the header in canonical files. Each 32-byte
entry is:

| Offset | Size | Field | Meaning |
|---:|---:|---|---|
| 0 | 4 | section_id | permanent ID |
| 4 | 4 | flags | section flags |
| 8 | 8 | offset | aligned payload start |
| 16 | 8 | length | payload bytes, excluding padding |
| 24 | 4 | element_count | logical records/items |
| 28 | 4 | element_size | fixed record width, or zero if variable |

Section flag `0x1` is `CRITICAL`; all other G1 bits are reserved. Directory
entries MUST be strictly increasing by section ID with no duplicates. Payloads
MUST be ordered the same way, begin at an 8-byte boundary, not overlap the header,
directory, or another payload, and lie within `file_size`. Padding bytes MUST be
zero. The last payload plus its zero padding MUST reach `file_size`; trailing
unaccounted data is forbidden.

G1 section IDs are:

| ID | Name | Required | Critical | Record form |
|---:|---|---|---|---|
| 1 | `STRINGS` | yes | yes | variable |
| 2 | `TYPES` | yes | yes | variable |
| 3 | `CONSTANTS` | yes | yes | variable |
| 4 | `SIGNATURES` | yes | yes | variable |
| 5 | `IMPORTS` | yes, may be empty | yes | 24 bytes |
| 6 | `PROTOCOLS` | yes, may be empty | yes | variable |
| 7 | `HANDLER_DEFS` | yes, may be empty | yes | variable |
| 8 | `FUNCTIONS` | yes | yes | 64 bytes |
| 9 | `CODE` | yes | yes | 4-byte words |
| 10 | `OPERANDS` | yes, may be empty | yes | 4-byte words |
| 11 | `CLEANUPS` | yes, may be empty | yes | 24 bytes |
| 12 | `EXPORTS` | yes, may be empty | yes | 16 bytes |
| 13 | `DROP_GLUE` | yes, may be empty | yes | 16 bytes |
| 14 | `FEATURES` | reserved, absent in G1 | yes | future |
| `0x80000001` | `DEBUG` | no | no | separately versioned |
| `0x80000002` | `BUILD_METADATA` | no | no | separately versioned |

Known required sections MUST carry `CRITICAL`; the two optional sections MUST
not. `element_count` MUST match the logical count described below.
`CODE` and `OPERANDS` use `element_size = 4` and count words. Fixed-record
sections use the record width shown in the table. Empty sections still contain
their format's count/offset prefix when one is specified.

### 3.3 Canonical placement and identity

A canonical writer emits the 64-byte header, directory, alignment padding, then
payloads in ID order. It emits all required sections including empty ones and
omits empty optional sections. Debug and build metadata do not participate in
program semantics. Reproducible compiler artifacts MUST omit them.

All strings are deduplicated and ordered lexicographically by UTF-8 byte sequence.
Source-defined nominal declarations, functions, protocols, and handlers receive
indices in resolved declaration order. Compiler-generated entries follow their
owning declaration in preorder by source span and then by creation-kind numeric
ID. Structural types/constants are deduplicated by their encoded form and ordered
by first deterministic use. This assignment algorithm is part of reproducible
compiler output; a decoder need not enforce provenance, only encoding validity.

## 4. Core tables

### 4.1 `STRINGS`

Payload:

```text
u32 count
u32 byte_length
u32 offsets[count + 1]
u8  bytes[byte_length]
```

`offsets[0]` MUST be zero, offsets MUST be nondecreasing, and
`offsets[count] == byte_length`. Each slice is one UTF-8 string. Duplicate strings
and non-lexicographic ordering are invalid. Directory `element_count == count`
and `element_size == 0`.

### 4.2 Variable-record sections

`TYPES`, `CONSTANTS`, `SIGNATURES`, `PROTOCOLS`, and `HANDLER_DEFS` use:

```text
u32 count
u32 offsets[count + 1]
u8  records[]
```

Offsets are relative to `records`, begin at zero, are strictly increasing, and
end at its byte length. Every record starts with:

```text
u8  tag
u8  flags
u16 reserved
u32 payload_length
u8  payload[payload_length]
```

The enclosing offset span MUST equal `8 + payload_length`; no record padding is
allowed. Directory `element_count == count`, `element_size == 0`.

### 4.3 `TYPES`

Type record flags are `0x01 DUPLICABLE`, `0x02 ZERO_SIZED`, `0x04 OPAQUE`,
`0x08 HAS_DROP`, and `0x10 ZERO_USE_ALLOWED`. No other bits are valid.
`DUPLICABLE` and `ZERO_USE_ALLOWED` are lowered principal-`Use` capabilities and
may be omitted to impose a stricter source discipline; when present, the verifier
also requires the runtime layout to support them. Shared references and immutable
scalars support duplication; unique references do not. A callable supports
`DUPLICABLE` only if all captures are duplicable, and independently supports
`ZERO_USE_ALLOWED` only if every capture permits zero use. Neither capability
implies the other: a relevant-but-copy environment remains non-droppable, while
an affine environment may be droppable without being copyable. A handler is
never duplicable in G1. A resumption supports duplication only under its
quantity and capture rules. `OPAQUE` is
required for binding packs, availability witnesses, and compiler-created
callable/handler/resumption identities. `HAS_DROP` requires both
`ZERO_USE_ALLOWED` and one matching `DROP_GLUE` entry: custom `Drop` is a hook
on a zero-use destruction path, never a substitute for transfer.

Type tags and exact payloads:

| Tag | Type | Payload |
|---:|---|---|
| `0x00` | `UNIT` | empty |
| `0x01` | `NEVER` | empty |
| `0x02` | `U8` | empty |
| `0x03` | `U16` | empty |
| `0x04` | `U32` | empty |
| `0x05` | `U64` | empty |
| `0x06` | `U128` | empty |
| `0x07` | `I8` | empty |
| `0x08` | `I16` | empty |
| `0x09` | `I32` | empty |
| `0x0a` | `I64` | empty |
| `0x0b` | `I128` | empty |
| `0x0c` | `USIZE` | empty; unsigned 64-bit semantics |
| `0x0d` | `ISIZE` | empty; signed 64-bit semantics |
| `0x0e` | `F32` | empty |
| `0x0f` | `F64` | empty |
| `0x10` | `CHAR` | empty Unicode scalar |
| `0x11` | `TEXT` | empty immutable UTF-8 |
| `0x12` | `BYTES` | empty immutable octets |
| `0x20` | `TUPLE` | `u32 count; u32 type[count]` |
| `0x21` | `ARRAY` | `u32 element_type` |
| `0x22` | `STRUCT` | `u32 name; u32 field_count; {u32 name,u32 type}[field_count]` |
| `0x23` | `ENUM` | `u32 name; u32 variant_count; Variant[variant_count]` |
| `0x24` | `REF_SHARED` | `u32 referent_type` |
| `0x25` | `REF_UNIQUE` | `u32 referent_type` |
| `0x26` | `CALLABLE` | `u32 signature; u32 capture_type; u32 receiver_mode; u32 identity_name` |
| `0x27` | `HANDLER` | `u32 handler_def; u32 capture_type; u32 identity_name` |
| `0x28` | `RESUMPTION` | descriptor below |
| `0x29` | `BINDING_PACK` | `u32 payload_type; u32 identity_name` |
| `0x2a` | `AVAILABLE` | `u32 identity_name` |
| `0x2b` | `STATIC_DATA` | `u32 element_type; u128 tag; u32 alignment` |

An enum `Variant` is:

```text
u32 name
u32 field_count
{ u32 name; u32 type; } fields[field_count]
```

The resumption payload is:

```text
u32 input_type
u32 output_type
u32 effect_signature
u32 lower_uses
u32 upper_kind       // 0 finite, 1 infinite
u32 upper_uses       // zero when upper_kind == 1
u32 identity_name
```

Finite `lower_uses <= upper_uses`; infinite upper accepts any lower. An upper
greater than one requires `MULTISHOT_G1`, a duplicable resumption descriptor, and
copy-verifiable captured state. `AVAILABLE` is always zero-sized, opaque, and
nonconstructible. `BINDING_PACK` is opaque but has the runtime layout and drop
behavior of its payload tuple.

`STATIC_DATA` is compiler-owned, immutable artifact data. Its `tag` is a stable
type identity, not a source spelling or MIME-like label; `alignment` is nonzero
and a power of two. It is always `DUPLICABLE|ZERO_USE_ALLOWED` and has no
user-source constructor. A static-data constant may be loaded only into the one
declared `STATIC_DATA` type with the same `(tag, alignment)` pair. The `element`
type controls the sealed shared-reference result of `static.get_shared`.

The predefined scalar records MUST appear first, exactly once, in tag order from
`UNIT` through `BYTES`. Recursive nominal references are allowed. Ignoring
references through `REF_*`, `CALLABLE`, `HANDLER`, and `RESUMPTION`, owned type
edges MUST be acyclic.

Consequently the scalar type IDs are permanently 0 through 18 in tag order.
`UNIT` has `DUPLICABLE|ZERO_SIZED|ZERO_USE_ALLOWED`; `NEVER` has `ZERO_SIZED`;
integer, float, character, text, and bytes types have
`DUPLICABLE|ZERO_USE_ALLOWED`. Other flags on these predefined records are
invalid.

### 4.4 `CONSTANTS`

Constant flags are zero. Tags are the scalar type tags `UNIT`, integer tags,
`F32`, `F64`, `CHAR`, `TEXT`, `BYTES`, and `STATIC_DATA` (`0x13`). Payloads are:

- unit: empty;
- integer: exactly its fixed-width two's-complement/raw bytes;
- `F32`/`F64`: 4/8 canonical IEEE bytes;
- `CHAR`: one `u32` Unicode scalar;
- `TEXT`: one `u32` string index;
- `BYTES`: `u32 length; u8 bytes[length]`;
- `STATIC_DATA`: `u128 tag; u32 alignment; u32 length; u8 bytes[length]`.

Constants MUST be deduplicated. They are ordered by `(tag, payload bytes)`.
`STATIC_DATA` alignment is nonzero and a power of two. A static segment's
constant-table index is its artifact-local segment identity; runtime subviews
retain that identity while changing only their checked byte offset and length.

### 4.5 `SIGNATURES`

Only tag 0, flags 0 is valid. Its payload is:

```text
u32 parameter_count
u32 result_type
u32 outward_protocol_count
u32 parameter_type[parameter_count]
u32 outward_protocol[outward_protocol_count]
```

Protocols are sorted ascending without duplicates. Closed executable entry
functions MUST have an empty outward protocol list. Effect rows are verifier
metadata and do not alter the calling convention.

### 4.6 Fixed tables

`IMPORTS` records (24 bytes):

```text
u32 capability_string
u32 symbol_string
u32 signature
u32 flags             // bit 0 MAY_TRAP; others zero
u64 reserved
```

Imports are sorted by `(capability bytes, symbol bytes, signature)` and unique.

`FUNCTIONS` records (64 bytes):

```text
u32 name
u32 signature
u32 flags
u32 register_count
u32 code_word_start
u32 code_word_length
u32 instruction_count
u32 cleanup_start
u32 cleanup_count
u32 label_slot_count
u32 capture_type
u32 receiver_mode       // NONE32 direct; 0 shared, 1 unique, 2 move
u64 reserved2
u64 reserved3
```

Function flags are `0x1 EXPORTED`, `0x2 DROP_HOOK`, and `0x4 NO_RETURN`. A drop
hook MUST have no outward protocols, label instructions, handler instructions,
perform/resume/cancel, or host calls; it MUST take exactly one unique reference
and return unit.

Register 0 is the hidden receiver slot. For a direct function it contains unit,
`capture_type == UNIT`, and `receiver_mode == NONE32`. For an indirect target it
contains a shared reference, unique reference, or moved value of `capture_type`
according to `receiver_mode`. Declared parameters initially occupy registers 1
through `parameter_count`; remaining registers are empty. `register_count` MUST
be at least `1 + parameter_count`. A source callable that supports multiple
receiver forms lowers to separate specialized function entries (small trampolines
MAY share a common direct body).

`CLEANUPS` records (24 bytes):

```text
u32 function
u32 first_instruction       // inclusive
u32 end_instruction         // exclusive
u32 operand_start           // register list in OPERANDS
u32 operand_count
u32 reserved
```

Records are sorted by function then `first_instruction`, do not overlap, and
cover every instruction ordinal in each nonempty function exactly once. Register
lists contain unique register IDs in destruction order (innermost/newest first).
Empty registers are skipped at runtime. Every listed register type must have
`ZERO_USE_ALLOWED`. A cleanup transition zero-destroys listed owners until its
verified destination boundary; nonzero-lower-bound owners must already have
been transferred or completely deconstructed and therefore be empty.

`EXPORTS` records (16 bytes):

```text
u32 name
u32 function
u32 signature
u32 flags             // zero
```

Exports are sorted by string bytes and have unique names. Their signature MUST
equal the function signature.

`DROP_GLUE` records (16 bytes):

```text
u32 type
u32 function
u32 flags             // zero
u32 reserved
```

Entries are sorted by type and unique. The type must have `ZERO_USE_ALLOWED`.
Structural destruction is supplied by the VM; `function` is only the custom hook
invoked first on an otherwise legal zero-use destruction path.

### 4.7 Protocol and handler tables

`PROTOCOLS` uses record tag 0, flags 0:

```text
u32 display_name
u32 type_argument_count
u32 type_argument[type_argument_count]
u32 operation_count
Operation operations[operation_count]
```

The protocol table index is the artifact's normalized runtime protocol key. The
display name is the resolved declaration identity and the arguments are the
normalized instantiated type IDs. Records are sorted by the UTF-8 bytes of
`display_name` and then lexicographically by the encoded type-argument list;
duplicates are invalid. Operations remain in
declaration order and are:

```text
u32 name
u32 payload_signature       // parameters are operation payloads
u32 result_type
u32 resumption_lower
u32 resumption_upper        // NONE32 means infinity
u32 flags                   // bit 0 TERMINAL; others zero
```

Terminality is declaration-site and requires `result_type == NEVER`,
the canonical quantity `[0,0]`, and `TERMINAL`. Nonterminal operations carry
only their declared resumption quantity; concrete resumption identities belong
to handler clauses.

`HANDLER_DEFS` uses record tag 0. Flag bit 0 is `PARTIAL`; no other bits are valid.
Payload:

```text
u32 result_type
u32 clause_count
Clause clauses[clause_count]
```

Each clause is:

```text
u32 protocol
u32 operation
u32 callable_signature
u32 resumption_type        // NONE32 for a terminal clause
```

Clauses are in source first-match order. Duplicate protocol/operation entries are
invalid: source pattern alternatives for one operation compile into the single
clause callable's decision DAG. A total handler must contain every operation of
every protocol it claims to handle; a partial handler forwards absent operations.
For terminal operations the callable parameters are the payload parameters. For
resumptive operations, `resumption_type` names a fresh nominal `RESUMPTION`
descriptor appended to the payload parameters. Its input is the operation
result, its output and effect-signature result are the handler result, its
effect-signature parameter list is empty, and its quantity exactly equals the
operation quantity. A concrete resumption type may belong to only one clause;
different handler definitions cannot alias the same anonymous identity. Every
clause returns the handler definition's `result_type`.

## 5. Instruction encoding

`CODE` and `OPERANDS` are arrays of little-endian `u32` words. Each instruction
starts with:

```text
bits  0..11  opcode
bits 12..19  inline operand count N
bits 20..31  instruction flags
followed by N u32 operands
```

All G1 instruction flags are zero. Operand count MUST equal the opcode's exact
count below. Function code ranges may not overlap and MUST decode to exactly the
declared instruction count. Branch targets are instruction ordinals within the
current function, never word offsets. An `(operand_start, operand_count)` pair
selects a range in `OPERANDS`.

`dst` operands name a register unless explicitly allowed to be `NONE32` for unit
or never results. Every nonempty register has exactly its statically inferred
type at each instruction. Arguments in `OPERANDS` are register IDs unless a
table's format says otherwise.

### 5.1 Values, ownership, and aggregates (`0x000`-`0x01f`)

| Opcode | Mnemonic | Operands | Semantics |
|---:|---|---|---|
| `0x000` | `NOP` | none | no effect |
| `0x001` | `CONST` | `dst, constant` | place a copy of constant in empty `dst` |
| `0x002` | `MOVE` | `dst, src` | move value; `src` becomes empty |
| `0x003` | `COPY` | `dst, src` | structurally duplicate a duplicable value |
| `0x004` | `BORROW_SHARED` | `dst, src` | shared borrow of whole live place |
| `0x005` | `BORROW_UNIQUE` | `dst, src` | unique borrow of whole live place |
| `0x006` | `REBORROW_SHARED` | `dst, src_ref` | shared reborrow of referenced place |
| `0x007` | `REBORROW_UNIQUE` | `dst, src_ref` | unique reborrow from unique reference |
| `0x008` | `END_BORROW` | `ref` | consume reference and end its loan |
| `0x009` | `CONSTRUCT` | `dst, type, variant, start, count` | move listed fields into aggregate; `variant=NONE32` except enum |
| `0x00a` | `PROJECT_MOVE` | `dst, aggregate, field` | move field; source field becomes empty |
| `0x00b` | `PROJECT_COPY` | `dst, aggregate, field` | copy duplicable field |
| `0x00c` | `PROJECT_BORROW_SHARED` | `dst, aggregate_or_ref, field` | shared field borrow |
| `0x00d` | `PROJECT_BORROW_UNIQUE` | `dst, aggregate_or_unique_ref, field` | unique field borrow |
| `0x00e` | `ENUM_TAG` | `dst, enum_value` | write active zero-based variant as `u32` |
| `0x00f` | `MAKE_CALLABLE` | `dst, callable_type, function, start, count` | move captures into the explicitly identified callable descriptor |
| `0x010` | `MAKE_HANDLER` | `dst, handler_def, start, count` | move one clause callable per definition entry |
| `0x011` | `DROP` | `src` | zero-use destroy; `src` type must allow zero |
| `0x012` | `MAKE_BINDING_PACK` | `dst, binding_type, start, count` | move runtime refinement payloads into an opaque binding pack |
| `0x013` | `DECONSTRUCT` | `src` | release an aggregate shell after every active initialized field moved |
| `0x014` | `DEREF_COPY` | `dst, src_ref` | copy the duplicable referent of a live shared or unique reference into empty `dst`; preserve the reference and its loan |
| `0x015` | `DEREF_MOVE` | `dst, src_unique_ref` | move the initialized referent into empty `dst`, leaving a temporary hole while preserving the unique reference and its loan |
| `0x016` | `DEREF_STORE` | `dst_unique_ref, src` | fill the temporary hole through the same unique loan by moving `src`; preserve the reference and consume `src` |

Projection `field` is zero-based in a tuple/struct or active enum payload. Enum
projection requires verifier-proven tag dominance. Constructed field types,
callable/handler capture tuples, and binding-pack payloads MUST match their
descriptors. `MAKE_CALLABLE` carries the exact nominal callable type so decoding
never guesses between equal-layout closure identities. Its function signature,
capture type, and receiver mode MUST exactly match that descriptor; receiver mode
is 0 shared, 1 unique, or 2 owned.
`AVAILABLE` fields are erased from runtime layouts and operand lists;
an `AVAILABLE` type may not occupy a register, appear in a signature, or be
projected. `DROP` calls custom glue exactly once, then destroys initialized active
fields in reverse declaration order, then releases storage. It is valid only
when `src` has `ZERO_USE_ALLOWED`; it contributes no ordinary owned use.
`DEREF_COPY` requires `src_ref` to have type `RefShared<T>` or `RefUnique<T>`,
requires `T` to be duplicable, and requires `dst` to have exactly type `T`. It
reads the live `ReferenceTarget` selected when the borrow or projection was
created. It neither consumes `src_ref` nor ends, downgrades, or transfers its
loan; a suspended parent reference is not readable until its child loan ends.

`DEREF_MOVE` and `DEREF_STORE` form the verified read-modify-write substrate for
assignment through `RefUnique<T>`. `DEREF_MOVE` requires an initialized,
unsuspended unique loan and exact destination type `T`; it preserves the
reference handle but marks its referent uninitialized. While that hole exists,
the referent cannot be read, moved again, copied, projected, or reborrowed, and
the reference cannot be ended, dropped, returned, passed to a call, or otherwise
consumed. `DEREF_STORE` requires that exact uninitialized unique loan and an
initialized `src: T`; it moves `src` into the hole and marks the referent
initialized again. It is invalid to overwrite an initialized referent. Control-
flow joins must agree on this initialization state. An `ABORT`, `UNREACHABLE`,
terminal effect, or other non-returning edge may terminate while a hole exists,
because no cleanup or reference consumption occurs on that edge.

`MOVE` of a whole owner is a `Transfer`. A sequence of `PROJECT_MOVE`
instructions is a `Deconstruct` only when frontend visibility and exhaustiveness
proofs exposed the complete layout and verifier dataflow accounts for every
initialized field of the proven active variant. Bound/projected fields become
independent owners. Any wildcard, omitted field, or otherwise unprojected
remainder is disposed with `DROP` and therefore must have
`ZERO_USE_ALLOWED`. An opaque or unproven enum layout may be transferred whole
but cannot be deconstructed.

`DECONSTRUCT` consumes only the empty aggregate shell. Its source must be a
tuple, struct, or enum whose active variant is verifier-known and whose complete
runtime field-initialization set is empty, and whose type does not have
`HAS_DROP`. A fieldless struct or proven fieldless active enum variant therefore
qualifies immediately only when it has no custom hook. `DECONSTRUCT` invokes no
custom hook and performs no recursive destruction, needs no
`ZERO_USE_ALLOWED`, and fails at runtime if a malformed unchecked execution
still presents an initialized field.

### 5.2 Calls and control (`0x020`-`0x03f`)

| Opcode | Mnemonic | Operands | Semantics |
|---:|---|---|---|
| `0x020` | `JUMP` | `target` | jump within function |
| `0x021` | `SWITCH` | `value, start, count, default` | compare against `(constant,target)` operand pairs in order |
| `0x022` | `CALL` | `dst, function, start, count` | direct call with moved arguments |
| `0x023` | `CALL_INDIRECT` | `dst, callable, receiver_mode, start, count` | call callable using the encoded receiver access |
| `0x024` | `TAIL_CALL` | `function, start, count` | cleanup and replace frame with direct callee |
| `0x025` | `TAIL_CALL_INDIRECT` | `callable, receiver_mode, start, count` | cleanup and replace frame with callable target |
| `0x026` | `RETURN` | `value` | return moved value; `NONE32` only for unit |
| `0x027` | `UNREACHABLE` | none | verifier-known unreachable; execution is a VM fault |
| `0x028` | `LABEL_PUSH` | `slot, result_reg, target` | install lexical destination |
| `0x029` | `LABEL_POP` | `slot` | remove innermost matching destination |
| `0x02a` | `LEAVE` | `slot, value` | cleanup to destination, move result, and jump |

Call arguments are listed left-to-right and are moved; callers explicitly copy or
borrow first when required. `receiver_mode` is 0 shared borrow, 1 unique borrow,
or 2 move. The selected callable descriptor and verifier state must permit that
mode. The descriptor and target function retain the body's canonical access
mode. An indirect call may request the same or a stronger mode (`requested >=
canonical`); the VM adapts the handle to the canonical receiver passed to the
body. A move request consumes the callable even when the body receives a shared
or unique reference, and destroys the captured environment after that call
returns. Borrowed requests preserve the callable handle. Direct calls require a
target whose receiver mode is `NONE32`. `TAIL_CALL_INDIRECT` requires move mode in G1;
a compiler may copy a duplicable callable to a temporary and move that temporary.
`dst` may be `NONE32` only for unit/never. A tail call first moves arguments and
any moved receiver to protected transfer slots, zero-destroys only remaining
caller-owned values whose types have `ZERO_USE_ALLOWED`, and replaces the frame;
it does not grow the VM stack. Switch constants must have the value's scalar
type, must be unique, and are tested in encoded order.

Label slots are function-local, less than `label_slot_count`, properly nested,
and never observable as values. `target` must be dominated by its push region's
exit, and no ordinary jump may enter that region. `LEAVE` uses the cleanup maps
to destroy frames/scopes between the current point and label boundary before
writing `result_reg` and branching. Concretely, the target cleanup list must be a
suffix of every reachable `LEAVE` cleanup list; `LEAVE` protects its result value,
zero-destroys the current-list prefix (whose types must all allow zero), and
leaves the common suffix live.

### 5.3 Effects, resumptions, host, and abort (`0x040`-`0x07f`)

| Opcode | Mnemonic | Operands | Semantics |
|---:|---|---|---|
| `0x040` | `HANDLE` | `dst, handler, body, start, count` | invoke body under a deep handler delimiter |
| `0x041` | `PERFORM` | `dst, protocol, operation, start, count` | transfer to nearest matching clause |
| `0x042` | `RESUME` | `dst, resumption, receiver_mode, value` | invoke captured continuation with operation result |
| `0x043` | `CANCEL` | `dst, resumption` | destroy captured continuation and return unit |
| `0x044` | `HOST_CALL` | `dst, import, start, count` | invoke granted typed host import |
| `0x045` | `PRIMITIVE` | `dst, primitive, start, count` | execute frozen portable primitive |
| `0x046` | `ABORT` | `message` | terminate worker immediately; no cleanup; `message` is string index or `NONE32` |
| `0x047` | `MAKE_HANDLER_SHARED` | `dst, handler_def, function_start, function_count, capture_start, capture_count` | move one incoming capture environment into verifier-backed per-clause receiver views |

`HANDLE` moves both the handler and body callable into a delimiter and moves the
listed arguments into the body call. Its normal result type equals the handler
result type. When the handled computation finishes, remaining handler/body state
is zero-destroyed before the result is written, so every remaining owner must
have `ZERO_USE_ALLOWED`. A handler value supplies clause
callables in definition order. The nearest matching clause is selected; a
partial miss searches outward. A closed executable with no match faults as
`UnhandledEffect`. A function containing `PERFORM` must declare that exact
instantiated protocol in `Function.outward_protocols`; calls may propagate only
protocols declared by the caller. The designated entry function declares no
outward protocols. Payload operands are moved into `PERFORM` only after their
left-to-right evaluation completes, and a resumptive destination is initialized
only if a matching clause eventually resumes the captured continuation.

`MAKE_HANDLER_SHARED` constructs the handler's clause callables together. Its
function list has exactly one entry per handler-definition clause, every listed
function has the clause's declared signature, and every function views the same
capture-environment type. The capture registers are moved exactly once into
that environment. A terminal clause has move receiver mode and atomically takes
the environment after the abandoned continuation is cleaned; destroying the
unselected callable aliases does not destroy or duplicate it. A resumptive
clause has a shared receiver whose referent is that environment, so it may
observe or borrow nonduplicable fields while the handler delimiter retains the
owner. It may not consume a nonduplicable field or obtain unique access. The
verifier checks the common layout, clause signatures, receiver modes, and
environment cleanup obligations. When a handled body may resume more than once,
the VM snapshots the handler as an object graph: all clauses in one replay keep
one shared environment identity, while different replays receive independent
graphs. Every cloned handler, callable, and environment node must be free of
custom `Drop`; the compiler must additionally prove that each capture's
principal `Use` contains the finite replay count, or has an unbounded upper
bound for unbounded replay. It requires `HANDLERS_G1`; multishot forms also
require `MULTISHOT_G1`.

`PERFORM` payload registers are already evaluated and listed left-to-right. For a
terminal operation `dst == NONE32`: the abandoned continuation is destroyed
before the clause begins and no resumption is passed. Every owner in that
abandoned continuation must have `ZERO_USE_ALLOWED`. For a resumptive operation,
frames through the delimiter are detached into the selected clause's resumption type and
passed after payload arguments. The instruction's result arrives in `dst` when
the continuation is resumed.

`RESUME` uses the same receiver-mode encoding as an indirect call. It MUST move a
one-shot resumption; a second use is impossible in verified code. Deep resumption
reinstalls its handler delimiter. A multi-shot resume may use a shared or unique
borrow only when the descriptor and captured state prove that mode sound.
The stored runtime identity must equal the register's concrete resumption type,
and the descriptor's outward effect row must be contained in the resuming
function's outward row.
`CANCEL` consumes the resumption and performs zero-use cleanup of all captured
frames before writing unit. Cancellation is invalid if any abandoned owner's
source-level lower use excluded zero; the
compiler proves that fact and the bytecode verifier enforces the emitted
resumption/copy metadata.
Dropping an unused `[0,1]` resumption through verified ordinary zero-use cleanup
has the same continuation-destruction semantics as `CANCEL`, without producing
the instruction's unit result. A positive-lower-bound resumption cannot take
that path.

### 5.4 Reserved opcode space

Opcodes `0x017`-`0x01f`, `0x02b`-`0x03f`, `0x048`-`0x07f`, and
`0x080`-`0x7ff` are unassigned standard extensions. `0x800`-`0xfff` are
permanently reserved and MUST never appear in portable artifacts. An unknown
opcode is always a verification error even when its numeric range is reserved;
future opcodes therefore require a declared feature understood by the VM.

## 6. Frozen primitive table

Primitive IDs are permanent. Unless named `wrapping`, integer overflow, division
by zero, invalid shift count, out-of-range conversion, invalid character, and
array bounds failure produce a catchless VM fault and perform no cleanup.
Arguments and result types are checked from the primitive ID.

| ID | Name |
|---:|---|
| `0x0000` | `int.checked_add` |
| `0x0001` | `int.checked_sub` |
| `0x0002` | `int.checked_mul` |
| `0x0003` | `int.checked_div` |
| `0x0004` | `int.checked_rem` |
| `0x0005` | `int.wrapping_add` |
| `0x0006` | `int.wrapping_sub` |
| `0x0007` | `int.wrapping_mul` |
| `0x0008` | `int.bit_and` |
| `0x0009` | `int.bit_or` |
| `0x000a` | `int.bit_xor` |
| `0x000b` | `int.bit_not` |
| `0x000c` | `int.shl` |
| `0x000d` | `int.shr` |
| `0x000e` | `int.eq` |
| `0x000f` | `int.ne` |
| `0x0010` | `int.lt` |
| `0x0011` | `int.le` |
| `0x0012` | `int.gt` |
| `0x0013` | `int.ge` |
| `0x0014` | `int.convert_checked` |
| `0x0015` | `int.convert_wrapping` |
| `0x0016` | `int.checked_neg` |
| `0x0017` | `int.wrapping_neg` |
| `0x0020` | `float.add` |
| `0x0021` | `float.sub` |
| `0x0022` | `float.mul` |
| `0x0023` | `float.div` |
| `0x0024` | `float.rem` |
| `0x0025` | `float.eq` |
| `0x0026` | `float.ne` |
| `0x0027` | `float.lt` |
| `0x0028` | `float.le` |
| `0x0029` | `float.gt` |
| `0x002a` | `float.ge` |
| `0x002b` | `float.convert` |
| `0x002c` | `float.neg` |
| `0x002d` | `int.to_float` |
| `0x002e` | `float.to_int_checked` |
| `0x002f` | `float.to_bits` |
| `0x0030` | `char.from_u32_checked` |
| `0x0031` | `char.to_u32` |
| `0x0032` | `float.from_bits` |
| `0x0040` | `text.byte_len` |
| `0x0041` | `text.concat` |
| `0x0042` | `text.eq` |
| `0x0043` | `text.from_utf8_checked` |
| `0x0044` | `text.as_bytes` |
| `0x0050` | `bytes.len` |
| `0x0051` | `bytes.concat` |
| `0x0052` | `bytes.get` |
| `0x0053` | `bytes.slice` |
| `0x0054` | `bytes.from_array_move` |
| `0x0055` | `bytes.to_array` |
| `0x0056` | `bytes.utf8_valid_up_to` |
| `0x0060` | `array.new` |
| `0x0061` | `array.len` |
| `0x0062` | `array.get_copy` |
| `0x0063` | `array.get_move` |
| `0x0064` | `array.get_borrow_shared` |
| `0x0065` | `array.get_borrow_unique` |
| `0x0066` | `array.set_move` |
| `0x0067` | `array.empty` |
| `0x0068` | `array.push_move` |
| `0x0069` | `array.pop_move` |
| `0x006a` | `array.capacity` |
| `0x006b` | `array.reserve` |
| `0x006c` | `array.finish_drained` |
| `0x0070` | `static.len` |
| `0x0071` | `static.subslice` |
| `0x0072` | `static.get_shared` |

`bytes.utf8_valid_up_to(Bytes) -> usize` returns the byte length when the input
is valid UTF-8. Otherwise it returns the byte offset of the invalid sequence's
lead byte, which is strictly less than the byte length.

Binary integer arithmetic/bit operations have `(T,T)->T`; shifts have
`(T,u32)->T`; integer negation has `(T)->T`; integer conversions have `(T)->U`.
Integer bit operations act on the `N`-bit two's-complement representation of
`T`. A shift count greater than or equal to `N` is invalid. Left shift discards
bits above bit `N-1`; unsigned right shift fills with zero, while signed right
shift is arithmetic and fills with the sign bit. Checked integer conversion
accepts exactly the mathematical values representable by `U`; wrapping integer
conversion retains the source value modulo `2^N`, where `N` is the width of
`U` (including sign reinterpretation of that resulting bit pattern).
Binary float arithmetic has `(F,F)->F`, float negation `(F)->F`, and numeric
conversion `(T)->U`. `float.to_int_checked` traps on NaN, infinity, or a value
outside `U`; `int.to_float` and `float.convert` use IEEE round-to-nearest
ties-to-even. Integer and float comparisons have `(T,T)->u32` and return exactly
0 or 1, not a language Boolean; the standard library converts that discriminator
to its result-based truth type. `float.to_bits` is exactly `f32->u32` or
`f64->u64`; `float.from_bits` is the inverse width pair. Every float-producing
primitive and both bit conversions canonicalize every NaN to the positive quiet
NaN (`0x7fc00000` or `0x7ff8000000000000`). Non-NaN bit patterns, including
positive and negative zero, are preserved by the bit round trip.

Character conversion has `u32->char` (trapping for a nonscalar) and `char->u32`.
Text operations are `byte_len(Text)->usize`, `concat(Text,Text)->Text`,
`eq(Text,Text)->u32`, `from_utf8_checked(Bytes)->Text`, and
`as_bytes(Text)->Bytes`. Byte operations are `len(Bytes)->usize`,
`concat(Bytes,Bytes)->Bytes`, `get(Bytes,usize)->u8`, and
`slice(Bytes,usize,usize)->Bytes`, where the last two indices are start and
exclusive end. `from_array_move(Array<u8>)->Bytes` consumes an array whose slots
are all initialized and implementations SHOULD reuse its allocation.
`to_array(Bytes)->Array<u8>` produces a mutable copy. The self-hosted compiler
builds output in `Array<u8>` and converts it once, avoiding quadratic immutable-
byte concatenation. Text indices are byte indices and any text boundary must be
UTF-8.

Runtime `Text` and `Bytes` values are shared immutable handles. `COPY`,
`DEREF_COPY`, and continuation snapshot cloning copy only the handle and MUST NOT
copy or reallocate its backing sequence. Operations that produce new text or
bytes allocate fresh immutable backing. `to_array` is deliberately the opposite
boundary: it creates independent mutable element storage with logical capacity
exactly equal to the byte length.

The three static-data primitives are sealed support for trusted standard-library
leaves, not public source-level slice types:

```text
static.len(__StaticData<T>) -> usize
static.subslice(__StaticData<T>, usize start, usize length) -> __StaticData<T>
static.get_shared(__StaticData<T>, usize index) -> &T
```

`subslice` checks `start + length <= current_length` without changing segment,
tag, alignment, or element type. `get_shared` checks `index < current_length`
and returns a shared reference to immutable static storage; it cannot be used
for a unique borrow or mutation. Standard-library `Str` and `Slice` wrappers may
use these leaves while remaining ordinary library types rather than compiler
intrinsics.

Array operations are:

```text
new(usize, T) -> Array<T>                 // fill is copied; T duplicable
len(&Array<T>) -> usize
get_copy(&Array<T>, usize) -> T           // T duplicable
get_move(&mut Array<T>, usize) -> T       // leaves an empty slot
get_borrow_shared(&Array<T>, usize) -> &T
get_borrow_unique(&mut Array<T>, usize) -> &mut T
set_move(&mut Array<T>, usize, T) -> ()   // target slot must be empty
empty<T>() -> Array<T>
push_move(&mut Array<T>, T) -> ()
pop_move(&mut Array<T>) -> T              // traps if empty or last slot empty
capacity(&Array<T>) -> usize
reserve(&mut Array<T>, usize) -> ()       // additional initialized elements
finish_drained(Array<T>) -> ()            // consumes only a fully drained shell
```

Array bounds and initialized-slot state are checked at runtime. Dropping an array
skips empty slots and destroys initialized elements in reverse index order, and
is therefore legal only when `T` has `ZERO_USE_ALLOWED`. `pop_move`, draining,
and `into_iter`/by-value iteration instead transfer initialized elements to their
caller and do not require zero-use evidence; an iterator may be abandoned with
elements remaining only when those elements allow zero.
`array.finish_drained` consumes its array argument by value and returns unit only
when every logical slot is uninitialized. If any initialized slot remains, it
produces a catchless primitive fault without running an element destructor or a
custom `Drop` hook. It therefore closes an array shell after `get_move` or
`pop_move` has transferred all element obligations, including when `T` does not
permit zero use. It does not make ordinary `DROP Array<T>` legal without
`T: ZERO_USE_ALLOWED` and cannot successfully dispose of a resident element.
`array.push_move` MUST use geometric capacity growth and therefore amortized
constant-time appends; the VM must not reallocate to exact length on every push.
`array.reserve(array, additional)` ensures capacity for at least
`len(array) + additional` slots without changing the length or initialized-slot
state. Addition overflow or a configured allocation-limit failure is a VM fault.

Array capacity is a logical, observable value independent of a host allocator's
physical allocation. `array.empty` has capacity zero; `array.new(n, value)` and
`bytes.to_array(bytes)` have capacity exactly their initial length. When growth is
required, `push_move` and `reserve` set logical capacity to the smallest power of
two at least the required length, with a minimum nonzero capacity of four. They
do not change logical capacity when the requested elements already fit. Overflow
while finding that capacity is a primitive trap. A VM may physically allocate
more memory but `array.capacity` returns only this frozen logical value.

## 7. Host ABI G1

Imports are resolved by exact `(capability, symbol, signature)`. The supervisor's
`--allow X` grants capability string `X`; no prefix or wildcard matching occurs.
Resolution and grants complete before the entry function starts. A host call may
return a value or a typed host fault. A host fault terminates execution without
Grandiose cleanup and is reported distinctly from verification, compatibility,
abort, and resource-limit failures.

The standard compiler host surface is:

| Capability | Symbol | Signature meaning |
|---|---|---|
| `process.args` | `get` | `() -> Array<Text>` |
| `fs.read` | `read` | `(Text) -> Bytes`, traps on access/I/O/size error |
| `fs.write` | `write` | `(Text, Bytes) -> Unit`, replace file atomically or trap |
| `diagnostic` | `write` | `(Text) -> Unit`, write UTF-8 diagnostic text |

The exact bytecode signature record must match these types. Paths are host-native
paths represented as UTF-8 text; unsupported paths trap. `fs.read` and `fs.write`
receive access only through separately granted capabilities. No environment,
clock, random, network, process creation, or ambient filesystem API exists in G1.
Host adapters MUST impose configured per-call allocation limits and MUST NOT expose
native addresses, descriptors, or mutable host buffers to bytecode.

## 8. Whole-artifact verification

Verification is mandatory and precedes execution. It performs at least:

1. header, feature, directory, section-bound, UTF-8, canonical-order, and reserved
   field validation;
2. complete table-reference and descriptor consistency checks;
3. owned-layout acyclicity, derived duplicability/zero-size/drop validation, and
   opaque-type construction restrictions;
4. instruction decoding, exact function ranges, branch boundaries, and opcode
   feature checks;
5. forward dataflow over register types and states (`Empty`, owned, shared loan,
   unique loan), requiring identical state at CFG joins;
6. legal move/copy/borrow/reborrow/end-borrow/projection and no access while
   incompatibly borrowed;
7. aggregate, direct/indirect call, return, tail-call, import, primitive,
   protocol, handler, and resumption signature agreement;
8. proper lexical nesting of label and handler regions, with no branch entering a
   region and no branch bypassing required cleanup;
9. cleanup-map coverage/order and proof that every owned runtime value is
   transferred whole, completely deconstructed, or destroyed exactly once with
   `ZERO_USE_ALLOWED` on every normal and nonlocal path;
10. dominance of enum-tag tests for payload projections and initialized active
    fields for every destruction;
11. one-shot resumption consumption, and for multi-shot resumptions duplicable
    captured frames, no unique loan, and duplicable handler dependencies;
12. drop-hook restrictions and absence of forged callable, handler, resumption,
    binding-pack, or availability values;
13. closed executable entry signature, empty outward effects, resolved granted
   imports, and exact export metadata.

`ABORT` is the sole disposition exception. It terminates the worker immediately
without cleanup, hooks, transfer, or deconstruction, so live registers need no
exit disposition proof on that edge. Catchless VM faults have the same runtime
termination behavior but cannot be used as a source-level disposal operation.

Opaque values may originate only from their dedicated VM operation: callable and
handler construction, effect capture, or `MAKE_BINDING_PACK`. `CONSTRUCT` MUST
reject an opaque destination. `AVAILABLE` is completely erased, has no register
state or materialization opcode, and may occur only as erased nominal field
metadata.

Verification success may produce a compact `VerifiedArtifact` with decoded
instructions, register states at block entries, checked indices, cleanup ranges,
and resolved imports. Straight-line per-instruction states MUST NOT be retained.
The executor accepts only this non-public capability type; raw decoded artifacts
cannot be executed. A loader SHOULD release the input buffer and temporary
verification workspaces once tables requiring borrowed bytes have been interned
or copied.

## 9. Runtime faults and deterministic behavior

VM faults are categorized as `Compatibility`, `Malformed`, `Verification`,
`UnhandledEffect`, `PrimitiveTrap`, `HostFault`, `ExplicitAbort`, `TimeLimit`,
`MemoryLimit`, and `Internal`. An `Internal` result is a VM bug and MUST never be
caused solely by artifact bytes.

Execution order, integer results, text/byte behavior, cleanup order, handler
selection, and float primitive operations are deterministic. Float operations use
IEEE round-to-nearest ties-to-even and canonicalize NaN results. VM-internal
hash-table iteration, host pointer size, locale, wall clock, and process
environment cannot affect portable execution. Host calls are explicitly outside deterministic
semantics; reproducible compilation therefore uses only deterministic file,
argument, and diagnostic inputs.

## 10. Release discipline

Before assigning an unassigned ID, a change must update this document, add its
feature bit, land VM decode/verify/execute support, and add a golden artifact.
Only then may a compiler emit it. Released IDs are never deleted, and every
released compiler seed remains in the newest VM's compatibility suite.

The native bootstrap tools negotiate released-seed compatibility before a
bytecode artifact is compiled, reused, or executed. `grc --capabilities`
advertises a versioned identity whose inputs are the compiler and VM contract
revisions, artifact major/minor, and supported feature mask; `grvm
--capabilities` advertises a sorted set of identities it accepts. The build
driver rejects partial metadata, protocol mismatches, or an unaccepted identity
before consulting cache freshness, fingerprints the complete compiler/VM/seed
tuple, and forwards the selected identity to `grvm run`, which checks it before
loading the artifact. A pre-negotiation compiler and VM may interoperate only
when both omit seed metadata. This deployment check does not add a field to the
G1 bytecode container or weaken normal decoder/verifier compatibility checks.

A bytecode extension is bootstrap-safe in this order:

1. new VM accepts old artifacts and implements the additive feature;
2. the previous compiler builds a bridge compiler using only old bytecode;
3. the bridge optionally emits the new feature;
4. compiler source adopts the feature only after the bridge seed is reproducible.

Canonical stage-2/stage-3 equality, golden encode/decode round trips, hostile
verification tests, MIR-before/after differential tests, and newest-VM/old-seed
execution are release gates.
