/-! Identifier lexemes for §3.1. Source syntax consumes the checked product;
no consumer invents its own character classification. UTF-8 decoding and token
boundaries are separate obligations; these functions classify decoded text. -/
namespace Grounded

def identifierStart (character : Char) : Bool :=
  decide (('a' ≤ character ∧ character ≤ 'z') ∨
    ('A' ≤ character ∧ character ≤ 'Z') ∨ character = '_')

def identifierContinue (character : Char) : Bool :=
  identifierStart character || decide ('0' ≤ character ∧ character ≤ '9')

/-- `_` is a wildcard/discard, never a readable source binding. Structural and
contextual keyword roles belong to the grammar, not this character predicate. -/
def identifierLexeme (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest => identifierStart first && rest.all identifierContinue && text != "_"

structure Identifier where
  text : String
  valid : identifierLexeme text = true
  deriving DecidableEq

/-- Total checked construction. Invalid text has no identifier product. -/
def Identifier.decode (text : String) : Option Identifier :=
  if valid : identifierLexeme text = true then some ⟨text, valid⟩ else none

/-- Decoding preserves the exact spelling and admits precisely the validated
lexeme. Proof fields never affect source-name equality. -/
theorem Identifier.decode_selected (text : String) (name : Identifier) :
    Identifier.decode text = some name ↔ name.text = text := by
  cases name with
  | mk spelling valid =>
    unfold Identifier.decode
    split
    next checked =>
      constructor
      · intro same
        exact (congrArg Identifier.text (Option.some.inj same)).symm
      · intro same
        change spelling = text at same
        subst spelling
        rfl
    next invalid =>
      constructor
      · intro impossible; cases impossible
      · intro same
        change spelling = text at same
        subst spelling
        exact False.elim (invalid valid)

theorem Identifier.decode_missing (text : String) :
    Identifier.decode text = none ↔ identifierLexeme text = false := by
  unfold Identifier.decode
  split <;> simp_all

/-- The executable classifier implements the specified character grammar,
including nonempty head/tail separation and the wildcard exclusion. -/
theorem identifierLexeme_grammar (text : String) : identifierLexeme text = true ↔
    ∃ first rest, text.toList = first :: rest ∧
      (('a' ≤ first ∧ first ≤ 'z') ∨ ('A' ≤ first ∧ first ≤ 'Z') ∨ first = '_') ∧
      (∀ character ∈ rest,
        (('a' ≤ character ∧ character ≤ 'z') ∨ ('A' ≤ character ∧ character ≤ 'Z') ∨
          character = '_') ∨ ('0' ≤ character ∧ character ≤ '9')) ∧ text ≠ "_" := by
  cases shape : text.toList with
  | nil => simp [identifierLexeme, shape]
  | cons first rest =>
    simp [identifierLexeme, shape, identifierStart, identifierContinue, Bool.and_eq_true,
      List.all_eq_true]
    constructor
    · intro ⟨⟨head, tail⟩, wildcard⟩
      exact ⟨first, rest, ⟨rfl, rfl⟩, head, tail, wildcard⟩
    · rintro ⟨other, others, ⟨rfl, rfl⟩, head, tail, wildcard⟩
      exact ⟨⟨head, tail⟩, wildcard⟩

end Grounded
