import GloriousLanguage.Target

/-! Arithmetic validity of the target's existing ordered layout producers.
These lemmas preserve padding and offsets; they do not choose another layout. -/
namespace Glorious.Language

theorem PowerOfTwo.positive {value : Nat} (power : PowerOfTwo value) : 0 < value := by
  obtain ⟨exponent,rfl⟩ := power
  exact Nat.pow_pos (by decide)

theorem PowerOfTwo.max {left right : Nat} (first : PowerOfTwo left) (second : PowerOfTwo right) :
    PowerOfTwo (max left right) := by
  rcases Nat.le_total left right with less | greater
  · simpa only [Nat.max_eq_right less] using second
  · simpa only [Nat.max_eq_left greater] using first

theorem alignUp.le {offset alignment : Nat} (positive : 0 < alignment) : offset ≤ alignUp offset alignment := by
  have remainder := Nat.mod_lt (offset + alignment - 1) positive
  have decomposed := Nat.mod_add_div' (offset + alignment - 1) alignment
  unfold alignUp
  omega

theorem alignUp.aligned (offset alignment : Nat) : alignUp offset alignment % alignment = 0 := by
  exact Nat.mul_mod_left _ _

theorem FieldsLayout.bounds {start stop : Nat} {fields : List Layout} {offsets : List Nat}
    (derived : FieldsLayout start fields offsets stop) : start ≤ stop ∧ ∀ offset ∈ offsets, offset ≤ stop := by
  induction derived with
  | nil => exact ⟨Nat.le_refl _,by intros; contradiction⟩
  | @cons offset field rest offsets stop valid _ ih =>
    have rounded := alignUp.le (offset := offset) valid.1.positive
    refine ⟨by omega,?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | inside
    · omega
    · exact ih.2 _ inside

theorem FieldsLayout.valid_fields {start stop : Nat} {fields : List Layout} {offsets : List Nat}
    (derived : FieldsLayout start fields offsets stop) : ∀ field ∈ fields, field.Valid := by
  induction derived with
  | nil => intros; contradiction
  | cons valid _ ih =>
    intro field member
    rcases List.mem_cons.mp member with rfl | inside
    · exact valid
    · exact ih _ inside

theorem Layout.maximum_alignment_power {fields : List Layout}
    (valid : ∀ field ∈ fields, field.Valid) {initial : Nat} (initialPower : PowerOfTwo initial) :
    PowerOfTwo (fields.foldl (fun alignment field => max alignment field.alignment) initial) := by
  induction fields generalizing initial with
  | nil => exact initialPower
  | cons field rest ih =>
    exact ih (fun field member => valid field (List.mem_cons_of_mem _ member))
      (initialPower.max (valid _ List.mem_cons_self).1)

theorem AggregateLayout.valid {fields : List Layout} {layout : Layout}
    (derived : AggregateLayout fields layout) : layout.Valid := by
  obtain ⟨stop,fields,alignment,size,_,_,_⟩ := derived
  have power : PowerOfTwo layout.alignment := alignment ▸
    Layout.maximum_alignment_power fields.valid_fields ⟨0,rfl⟩
  refine ⟨power,?_,?_⟩
  · rw [size]; exact alignUp.aligned _ _
  · intro offset member
    exact Nat.le_trans (fields.bounds.2 _ member) (size ▸ alignUp.le power.positive)

theorem ArrayLayout.valid {element : Layout} {count : Nat} {layout : Layout}
    (array : ArrayLayout element count layout) : layout.Valid := by
  obtain ⟨valid,rfl⟩ := array
  refine ⟨valid.1,?_,?_⟩
  · change (count * alignUp element.size element.alignment) % element.alignment = 0
    rw [alignUp,← Nat.mul_assoc,Nat.mul_mod_left]
  · intro offset member
    obtain ⟨index,inRange,rfl⟩ := List.mem_map.mp member
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt (List.mem_range.mp inRange))

theorem EnumLayout.valid {variants : List Layout} {layout : Layout}
    (derived : EnumLayout variants layout) : layout.Valid := by
  obtain ⟨_,variantsValid,tag,_,_,alignment,_,size,offsets,_⟩ := derived
  have tagPower : PowerOfTwo layout.tagBytes := by
    simp at tag
    rcases tag with tag | tag | tag | tag | tag
    · exact ⟨0,tag⟩
    · exact ⟨1,tag⟩
    · exact ⟨2,tag⟩
    · exact ⟨3,tag⟩
    · exact ⟨4,tag⟩
  refine ⟨alignment ▸ tagPower.max (Layout.maximum_alignment_power variantsValid ⟨0,rfl⟩),?_,?_⟩
  · rw [size]; exact alignUp.aligned _ _
  · intro offset member
    rw [offsets] at member
    cases member

end Glorious.Language
