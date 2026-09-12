import GloriousLanguage.DeclarationDependencyKinding

/-! Transport of the existing greatest structural component through a term
map. Different source types may become the same target type; their image
capability is the greatest class with an actual source witness, not an
arbitrary inverse choice or a fabricated permission for an empty fiber. -/
namespace Glorious.Language

/-- The image is supported by actual finite unfoldings. Each expansion and
logical leaf remains in that finite proof; only structural dependencies may
return to the greatest assignment. Empty image fibers grant no permission. -/
theorem CapabilityEvidence.image_coinduction {program : Program} {context : Context}
    (map : Term → Term) (domain : Term → Prop)
    {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (admitted : domain type) (found : assignment type = some principal)
    (unfolded : ∀ image,
      (∀ term claimed, domain term → assignment term = some claimed →
        ∃ result, image (map term) = some result ∧ claimed.Restricts result) →
      ∀ term claimed, domain term → assignment term = some claimed →
        CapabilityUnfolds program context image (map term) claimed) :
    CapabilityEvidence program context (map type) principal := by
  let image : Term → Option Principal := fun target =>
    Principal.greatest (fun claimed => ∃ source, domain source ∧ map source = target ∧ assignment source = some claimed)
  have imageUpper : ∀ term claimed, domain term → assignment term = some claimed →
      ∃ result, image (map term) = some result ∧ claimed.Restricts result := by
    intro term claimed admitted selected
    exact Principal.greatest_upper ⟨term,admitted,rfl,selected⟩
  obtain ⟨greatest,selected,ordered⟩ := imageUpper type principal admitted found
  apply CapabilityEvidence.restrict (last := greatest) ?_ ordered
  apply CapabilityEvidence.structural (assignment := image) selected
  intro target claimed imageFound
  obtain ⟨source,sourceAdmitted,rfl,sourceFound⟩ := Principal.greatest_origin imageFound
  exact unfolded image imageUpper source claimed sourceAdmitted sourceFound

/-- The coinductive transport boundary permits noninjective term maps.
The equation premise concerns one actual structural layer under an enlarged
assignment; logical leaves must already have their target derivations. This
is the precise interface needed by the mutual substitution proof. -/
theorem CapabilityEvidence.map_coinduction {sourceProgram targetProgram : Program} {targetContext : Context}
    (map : Term → Term) (domain : Term → Prop)
    {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (admitted : domain type) (found : assignment type = some principal)
    (unfolded : ∀ term claimed, domain term → assignment term = some claimed → ∃ supported,
      claimed.Restricts supported ∧
        (CapabilityEquation sourceProgram assignment term supported ∨
          CapabilityEvidence targetProgram targetContext (map term) supported))
    (equations : ∀ targetAssignment,
      (∀ term claimed, domain term → assignment term = some claimed →
        ∃ result, targetAssignment (map term) = some result ∧ claimed.Restricts result) →
      ∀ term supported, domain term → CapabilityEquation sourceProgram assignment term supported → ∃ result,
        supported.Restricts result ∧ CapabilityEquation targetProgram targetAssignment (map term) result) :
    CapabilityEvidence targetProgram targetContext (map type) principal := by
  apply CapabilityEvidence.image_coinduction map domain admitted found
  intro image imageUpper source claimed sourceAdmitted sourceFound
  obtain ⟨supported,sourceOrder,equation | evidence⟩ := unfolded source claimed sourceAdmitted sourceFound
  · obtain ⟨result,targetOrder,mapped⟩ := equations image imageUpper source supported sourceAdmitted equation
    exact .equation (sourceOrder.trans targetOrder) mapped
  · exact .evidence sourceOrder evidence

/-- Context transport leaves structural equations unchanged while replacing
only their actual logical leaves. It is the identity-map specialization of
the same noninjective transport theorem. -/
theorem CapabilityEvidence.transport_coinduction {program : Program} {context : Context}
    {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (found : assignment type = some principal)
    (unfolded : ∀ term claimed, assignment term = some claimed → ∃ supported,
      claimed.Restricts supported ∧
        (CapabilityEquation program assignment term supported ∨ CapabilityEvidence program context term supported)) :
    CapabilityEvidence program context type principal := by
  apply CapabilityEvidence.map_coinduction (map := id) (domain := fun _ => True) True.intro found
    (fun term claimed _ => unfolded term claimed)
  intro targetAssignment related term supported _ equation
  obtain ⟨result,mapped,ordered⟩ := equation.monotone (fun term claimed => related term claimed True.intro)
  exact ⟨result,ordered,mapped⟩

/-- Context transport of a kinded structural component keeps only its
admitted type dependencies. The source shape repair is consumed here through
the actual equation's kind-restricted monotonicity theorem. -/
theorem CapabilityEvidence.transport_kinded_coinduction {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (kinded : Kinding program source type .type) (found : assignment type = some principal)
    (unfolded : ∀ term claimed, Kinding program source term .type → assignment term = some claimed → ∃ supported,
      claimed.Restricts supported ∧
        (CapabilityEquation program assignment term supported ∨ CapabilityEvidence program target term supported)) :
    CapabilityEvidence program target type principal := by
  apply CapabilityEvidence.map_coinduction (map := id) (domain := fun term => Kinding program source term .type)
    kinded found unfolded
  intro targetAssignment related term supported admitted equation
  obtain ⟨result,mapped,ordered⟩ := equation.monotone_kinded valid admitted related
  exact ⟨result,ordered,mapped⟩

end Glorious.Language
