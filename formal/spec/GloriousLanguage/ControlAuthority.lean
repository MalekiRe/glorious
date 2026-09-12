import GloriousLanguage.ControlSupport

/-! Historical authority provenance of the same executable control products.
Recording means that a loan identity has an actual table entry, including
after it ends. It is not liveness, permission, or a second loan inventory. -/
namespace Glorious.Language

theorem Authority.Recorded.loan_bound {world : World} {authority : Authority} {id : Identity}
    (well : world.WellFormed) (recorded : authority.Recorded world.loans)
    (parent : authority.parentLoan = some id) : id < world.nextLoan := by
  obtain ⟨loan,found⟩ := recorded.parentLoan parent
  exact World.loanBounds well found

def AuthoritySupport.Recorded (authorities : List Authority) (loans : Table Loan) : Prop :=
  ∀ authority ∈ authorities, authority.Recorded loans

theorem AuthoritySupport.Recorded.mono {authorities : List Authority} {before after : Table Loan}
    (recorded : AuthoritySupport.Recorded authorities before)
    (retained : ∀ (authority : Authority), authority.Recorded before → authority.Recorded after) :
    AuthoritySupport.Recorded authorities after :=
  fun authority member => retained authority (recorded authority member)

@[simp] theorem AuthoritySupport.recorded_nil (loans : Table Loan) : Recorded [] loans := by
  simp [Recorded]

@[simp] theorem AuthoritySupport.recorded_cons {authority : Authority} {authorities : List Authority}
    {loans : Table Loan} : Recorded (authority :: authorities) loans ↔ authority.Recorded loans ∧ Recorded authorities loans := by
  simp [Recorded]

@[simp] theorem AuthoritySupport.recorded_append {left right : List Authority} {loans : Table Loan} :
    Recorded (left ++ right) loans ↔ Recorded left loans ∧ Recorded right loans := by
  simp [Recorded,or_imp,forall_and]

@[simp] theorem AuthoritySupport.recorded_map {α : Type} {items : List α}
    {authority : α → Authority} {loans : Table Loan} :
    Recorded (items.map authority) loans ↔ ∀ item ∈ items, (authority item).Recorded loans := by
  simp only [Recorded,List.mem_map]
  constructor
  · intro recorded item member
    exact recorded _ ⟨item,member,rfl⟩
  · rintro recorded current ⟨item,member,rfl⟩
    exact recorded item member

@[simp] theorem AuthoritySupport.recorded_flatMap {α : Type} {items : List α}
    {support : α → List Authority} {loans : Table Loan} :
    Recorded (items.flatMap support) loans ↔ ∀ item ∈ items, Recorded (support item) loans := by
  simp only [Recorded,List.mem_flatMap]
  constructor
  · intro recorded item member authority inside
    exact recorded authority ⟨item,member,inside⟩
  · rintro recorded authority ⟨item,member,inside⟩
    exact recorded item member authority inside

end Glorious.Language
