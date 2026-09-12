import GloriousLanguage.LayoutValidity
import GloriousLanguage.LogicalCut

/-! Layout evidence transports through the actual logical cut relation.
Runtime metadata changes cannot introduce assumptions or a new kinding domain. -/
namespace Glorious.Language

theorem LayoutOf.cut {program : Program} {source target : Context} {type : Term} {layout : Layout}
    (derived : LayoutOf program source type layout)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    LayoutOf program target type layout := by
  apply LayoutOf.rec
    (motive_1 := fun type layout _ => LayoutOf program target type layout)
    (motive_2 := fun types layout _ => FieldsHaveLayout program target types layout)
    (motive_3 := fun type layout _ => CCompatible program target type layout)
    (motive_4 := fun types layouts _ => ListRel (LayoutOf program target) types layouts)
    (motive_5 := fun types layouts _ => ListRel (FieldsHaveLayout program target) types layouts)
    (motive_6 := fun types layouts _ => ListRel (CCompatible program target) types layouts)
    <;> try assumption
  all_goals intros
  all_goals first
    | exact .unit
    | exact .scalar (by assumption)
    | exact .reference
    | exact .pointer
    | exact .tuple (by assumption) (by assumption)
    | exact .callable (by assumption) (by assumption) (by assumption)
    | exact .continuation
    | exact .label
    | exact .available
    | exact .bindings (by assumption) (by assumption)
    | exact .environment (by assumption) (by assumption)
    | exact .array (by assumption) (by assumption) (by assumption) (by assumption)
    | exact .nominal (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption)
    | exact .transparent (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption)
    | exact .cRepresentation (by assumption) (by assumption) (by assumption)
    | exact .fields (by assumption) (by assumption)
    | exact .record (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    | exact .enumeration (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    | exact .transparent (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    | exact .nil
    | exact .cons (by assumption) (by assumption)
    | { rename_i equal _ ih; exact .alias (equal.cut kinds assumptions) ih }

theorem LayoutOf.cut_same_domain {program : Program} {source target : Context} {type : Term} {layout : Layout}
    (derived : LayoutOf program source type layout) (binders : source.binders = target.binders)
    (levels : source.universeLevel = target.universeLevel) (scope : source.scope = target.scope)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    LayoutOf program target type layout :=
  derived.cut (fun _ _ => ⟨fun typed => typed.context_same_domain binders levels scope,
    fun typed => typed.context_same_domain binders.symm levels.symm scope.symm⟩) assumptions

theorem LayoutOf.runtime_context {program : Program} {sourceModule targetModule : ModuleId}
    {sourceUnsafe targetUnsafe : Bool} {type : Term} {layout : Layout}
    (derived : LayoutOf program ⟨[],[],0,sourceModule,sourceUnsafe,{}⟩ type layout) :
    LayoutOf program ⟨[],[],0,targetModule,targetUnsafe,{}⟩ type layout :=
  derived.cut_same_domain rfl rfl rfl (by intros; contradiction)

end Glorious.Language
