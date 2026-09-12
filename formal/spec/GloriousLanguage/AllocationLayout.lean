import GloriousLanguage.LayoutContext
import GloriousLanguage.LayoutExecution

/-! The real allocation producer admits only assumption-free layout evidence.
Logical cut carries its retained caller metadata into encoding and layout
queries; physical extent admission supplies actual pointer-integer bounds. -/
namespace Glorious.Language

theorem Allocates.layoutOf {program : Program} {before after : World}
    {home : Home} {region : Identity} {type : Term} {layout : Layout} {mutable : Bool} {address : Address}
    (allocated : Allocates program before home region type layout mutable address after)
    {module : ModuleId} {unsafeAllowed : Bool} :
    LayoutOf program ⟨[],[],0,module,unsafeAllowed,{}⟩ type layout := by
  cases allocated with
  | fresh _ _ _ _ source _ _ _ _ =>
    obtain ⟨sourceModule,sourceUnsafe,derived⟩ := source
    exact derived.runtime_context

theorem Allocates.representable {program : Program} {before after : World}
    {home : Home} {region : Identity} {type : Term} {layout : Layout} {mutable : Bool} {address : Address}
    (allocated : Allocates program before home region type layout mutable address after) :
    IntegerRange program.input.target false .pointer layout.size ∧
      IntegerRange program.input.target false .pointer layout.alignment := by
  cases allocated with
  | @fresh base _ _ _ _ _ positive aligned extent _ =>
    have alignmentBound : layout.alignment ≤ base := Nat.le_of_dvd positive (Nat.dvd_of_mod_eq_zero aligned)
    have sizeBound : layout.size < 2^program.input.target.pointerBits := by omega
    have alignBound : layout.alignment < 2^program.input.target.pointerBits := by omega
    have admitted : ∀ value : Nat, value < 2^program.input.target.pointerBits →
        IntegerRange program.input.target false .pointer value := by
      intro value bounded
      have cast : (value : Int) < ((2^program.input.target.pointerBits : Nat) : Int) := Int.ofNat_lt.mpr bounded
      exact ⟨Int.natCast_nonneg _,by
        simpa [integerLimit,Width.bits,Int.natCast_pow] using cast⟩
    exact ⟨admitted _ sizeBound,admitted _ alignBound⟩

theorem Allocates.query_layout_unique {program : Program} (valid : ProgramWellFormed program)
    {before after : World} {home : Home} {region : Identity} {type : Term} {layout other : Layout}
    {mutable : Bool} {address : Address} {module : ModuleId} {unsafeAllowed : Bool}
    (allocated : Allocates program before home region type layout mutable address after)
    (query : LayoutOf program ⟨[],[],0,module,unsafeAllowed,{}⟩ type other) : layout = other :=
  allocated.layoutOf.unique valid rfl query

theorem Allocates.encoding_layout_unique {program : Program} (valid : ProgramWellFormed program)
    {before after world : World} {home : Home} {region : Identity} {value : Value} {layout other : Layout}
    {mutable : Bool} {address encodedAddress : Address} {runtime : Memory.RuntimeAddresses} {bytes : List (Option Nat)}
    (allocated : Allocates program before home region value.type layout mutable address after)
    (encoded : Memory.Encodes program world runtime encodedAddress value other bytes) : layout = other :=
  allocated.query_layout_unique valid encoded.layoutOf

namespace Execution

/-- An actually admitted allocation of the queried type supplies the layout
and its usize bounds. No separate representability premise is needed here. -/
theorem Step.layout_allocated_safe_unique_progress {program : Kernel.Program} {host : Foreign.Model}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before : State} (typed : Typing.WorldTyped program before.world)
    {context : Context} {destination : Address} {binding : RuntimeBinding} {type : Term} {next : Kernel.Code}
    {allocationBefore allocationAfter : World} {home : Home} {region : Identity} {layout : Layout}
    {mutable : Bool} {address : Address}
    (allocated : Allocates program.declarations allocationBefore home region type layout mutable address allocationAfter)
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout)
    (destinationType : DestinationType before.world destination
      (.tuple [.scalar (.integer false .pointer),.scalar (.integer false .pointer)])) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      ∀ event other, Step program host before event other → event = none ∧ other = after :=
  Step.layout_safe_unique_progress valid inventory typed task identity allocated.layoutOf
    allocated.representable destinationType

end Execution

end Glorious.Language
