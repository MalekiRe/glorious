import GloriousLanguage.LayoutCoherence
import GloriousLanguage.Memory

/-! Runtime representation consumes the ordinary conversion-coherent layout
judgment. These results concern actual encodings; they neither select arbitrary
padding bytes nor assume every type has a representable object layout. -/
namespace Glorious.Language.Memory

theorem integerBytes.length (endian : Endianness) (width value : Nat) :
    (integerBytes endian width value).length = width := by
  cases endian <;> simp [integerBytes]

theorem integerBytes.byte_lt {endian : Endianness} {width value byte : Nat}
    (member : byte ∈ integerBytes endian width value) : byte < 256 := by
  cases endian <;> simp only [integerBytes,List.mem_reverse] at member
  all_goals obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  all_goals exact Nat.mod_lt _ (by decide)

theorem ScalarValue.bytes_length (target : TargetProfile) (scalar : Language.ScalarValue) :
    (ScalarValue.bytes target scalar).length = scalar.type.bytes target := by
  cases scalar with
  | integer => simp [ScalarValue.bytes,Language.ScalarValue.type,Scalar.bytes,integerBytes.length]
  | floating width bits => cases width <;>
      simp [ScalarValue.bytes,Language.ScalarValue.type,Scalar.bytes,integerBytes.length]
  | character => simp [ScalarValue.bytes,Language.ScalarValue.type,Scalar.bytes,integerBytes.length]

theorem ScalarValue.byte_lt {target : TargetProfile} {scalar : Language.ScalarValue} {byte : Nat}
    (member : byte ∈ ScalarValue.bytes target scalar) : byte < 256 := by
  cases scalar <;> exact integerBytes.byte_lt member

theorem Encodes.layoutOf {program : Program} {world : World} {runtime : RuntimeAddresses}
    {address : Address} {value : Value} {layout : Layout} {bytes : List (Option Nat)}
    (encoded : Encodes program world runtime address value layout bytes) :
    LayoutOf program ⟨[],[],0,default,false,{}⟩ value.type layout := by
  cases encoded <;> try assumption
  case unit => exact .unit
  case continuation => exact .continuation
  case proof shape =>
    rcases shape with ⟨_,_,_,_,type⟩ | ⟨_,_,_,_,_,type⟩
    · rw [type]; exact .label
    · rw [type]; exact .available

theorem Encodes.bytes_length {program : Program} (valid : ProgramWellFormed program)
    {world : World} {runtime : RuntimeAddresses} {address : Address} {value : Value}
    {layout : Layout} {bytes : List (Option Nat)}
    (encoded : Encodes program world runtime address value layout bytes) : bytes.length = layout.size := by
  cases encoded <;> try assumption
  all_goals try rfl
  all_goals try simp only [List.length_map,integerBytes.length]
  case scalar scalar layout _ derived =>
    have chosen := derived.scalar_unique valid rfl .refl
    simp only [ScalarValue.bytes_length,chosen]

theorem Encodes.layout_valid {program : Program} (valid : ProgramWellFormed program)
    {world : World} {runtime : RuntimeAddresses} {address : Address} {value : Value}
    {layout : Layout} {bytes : List (Option Nat)}
    (encoded : Encodes program world runtime address value layout bytes) : layout.Valid :=
  encoded.layoutOf.valid valid

theorem Encodes.layout_unique {program : Program} (valid : ProgramWellFormed program)
    {world : World} {runtime : RuntimeAddresses} {address : Address} {value : Value}
    {left right : Layout} {firstBytes secondBytes : List (Option Nat)}
    (first : Encodes program world runtime address value left firstBytes)
    (second : Encodes program world runtime address value right secondBytes) : left = right :=
  first.layoutOf.unique valid rfl second.layoutOf

theorem Encodes.convertible_layout_unique {program : Program} (valid : ProgramWellFormed program)
    {world otherWorld : World} {runtime otherRuntime : RuntimeAddresses} {address otherAddress : Address}
    {value otherValue : Value} {left right : Layout} {firstBytes secondBytes : List (Option Nat)}
    (first : Encodes program world runtime address value left firstBytes)
    (equal : DefinitionallyEqual program ⟨[],[],0,default,false,{}⟩ value.type otherValue.type)
    (second : Encodes program otherWorld otherRuntime otherAddress otherValue right secondBytes) : left = right :=
  first.layoutOf.unique_convertible valid rfl equal second.layoutOf

end Glorious.Language.Memory
