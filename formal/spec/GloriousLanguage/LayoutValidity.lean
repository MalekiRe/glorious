import GloriousLanguage.Static
import GloriousLanguage.TargetLayoutValidity

/-! Every actual ordinary/C layout is arithmetically valid. C integer enums
consume the same exact scalar mapping as ordinary C scalar arguments. -/
namespace Glorious.Language

theorem TargetProfile.Valid.scalar_layout {target : TargetProfile} (valid : target.Valid)
    {scalar : Scalar} (supported : scalar.Valid target) :
    (Layout.mk (scalar.bytes target) (target.scalarAlignment scalar) [] 0 0 []).Valid :=
  ⟨(valid.2.2.1 scalar supported).1,(valid.2.2.1 scalar supported).2,by intros; contradiction⟩

theorem TargetProfile.Valid.pointer_layout {target : TargetProfile} (valid : target.Valid) :
    (Layout.mk (target.pointerBits / 8) (target.pointerBits / 8) [] 0 0 []).Valid := by
  have bits := valid.1
  simp at bits
  have power : PowerOfTwo (target.pointerBits / 8) := by
    rcases bits with bits | bits | bits | bits
    · exact ⟨1,by rw [bits]⟩
    · exact ⟨2,by rw [bits]⟩
    · exact ⟨3,by rw [bits]⟩
    · exact ⟨4,by rw [bits]⟩
  exact ⟨power,Nat.mod_self _,by intros; contradiction⟩

theorem FieldsHaveLayout.valid {program : Program} {context : Context} {types : List Term} {layout : Layout}
    (derived : FieldsHaveLayout program context types layout) : layout.Valid := by
  cases derived with
  | fields _ aggregate => exact aggregate.valid

theorem LayoutOf.valid {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {type : Term} {layout : Layout} (derived : LayoutOf program context type layout) :
    layout.Valid := by
  have target : program.input.target.Valid := valid.1.1.2.2.2.2.1
  apply LayoutOf.rec
    (motive_1 := fun _ layout _ => layout.Valid)
    (motive_2 := fun _ layout _ => layout.Valid)
    (motive_3 := fun _ layout _ => layout.Valid)
    (motive_4 := fun _ layouts _ => ∀ layout ∈ layouts, layout.Valid)
    (motive_5 := fun _ layouts _ => ∀ layout ∈ layouts, layout.Valid)
    (motive_6 := fun _ layouts _ => ∀ layout ∈ layouts, layout.Valid)
    <;> try assumption
  all_goals intros
  all_goals try assumption
  all_goals try exact ⟨⟨0,rfl⟩,rfl,by intros; contradiction⟩
  all_goals try exact target.pointer_layout
  all_goals try exact target.scalar_layout (by assumption)
  all_goals try { rename_i aggregate _; exact aggregate.valid }
  all_goals try { rename_i aggregate; exact aggregate.valid }
  all_goals try { intros; contradiction }
  all_goals try {
    rename_i valid rest layout member
    rcases List.mem_cons.mp member with rfl | inside
    · exact valid
    · exact rest _ inside }
  case continuation => exact target.2.2.2.2.2.2.1.1
  case nominal =>
    rename_i choices _ variants
    rcases choices with ⟨_,enumeration⟩ | ⟨_,rfl⟩
    · exact enumeration.valid
    · exact variants _ List.mem_cons_self
  case transparent =>
    rename_i selected _ _ shape fields
    rw [shape]
    have represented := fields _ (List.mem_of_getElem? selected)
    exact ⟨represented.1,represented.2.1,by
      intro offset member
      have zero : offset = 0 := List.eq_of_mem_replicate member
      subst offset
      exact Nat.zero_le _⟩
  case scalar =>
    rename_i mapping
    simpa only [mapping.2.2] using target.scalar_layout mapping.1
  case record =>
    rename_i record _
    exact record.2.2.1
  case enumeration =>
    rename_i mapping _ _
    have scalar := target.scalar_layout mapping.1
    exact ⟨mapping.2.2 ▸ scalar.1,mapping.2.2 ▸ scalar.2.1,by intros; contradiction⟩

theorem CCompatible.layoutOf {program : Program} {context : Context} {type : Term} {layout : Layout}
    (compatible : CCompatible program context type layout) : LayoutOf program context type layout := by
  apply CCompatible.rec
    (motive_1 := fun _ _ _ => True) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun type layout _ => LayoutOf program context type layout)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case scalar scalar mapping =>
    simpa only [mapping.2.2] using (LayoutOf.scalar (program := program) (context := context) mapping.1)
  case pointer => exact .pointer
  case record _ _ _ _ _ _ _ _ found representation enumeration variants instantiated graph fields layout _ =>
    exact .cRepresentation found (Or.inl representation)
      (.record found representation enumeration variants instantiated graph fields layout)
  case enumeration _ _ _ _ _ _ found instantiated representation enumeration variants scalar fields range =>
    exact .cRepresentation found (Or.inr ⟨_,_,representation⟩)
      (.enumeration found instantiated representation enumeration variants scalar fields range)
  case transparent => assumption
  case alias _ _ _ equal _ ih => exact .alias equal ih

theorem CCompatible.valid {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {type : Term} {layout : Layout} (derived : CCompatible program context type layout) :
    layout.Valid := derived.layoutOf.valid valid

end Glorious.Language
