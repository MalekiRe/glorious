import Glorious.Semantics.Normalize

/-! Kernel-checked regressions for the public substitution producer and its
real constraint/signature consumers. No alternate substitution implementation. -/
open Glorious Glorious.Semantics

namespace SubstitutionRegression

def typeArg : Term := .scalar (.integer false .w32)
def sizeArg : Term := .constant (.integer false .pointer 3)
def effectArg : Term := .effect ⟨0, 7⟩ [typeArg]
def rowArg : Term := .row [effectArg] []
def brandArg : Term := .rigid 31 .brand 2
def replacements : Substitution :=
  [(1, typeArg), (2, .staticRegion), (3, sizeArg), (4, effectArg), (5, rowArg), (6, brandArg)]

/-- All term constructors, including both lists in split child sequences. -/
def carriers (type region size effect row brand : Term) : List Term :=
  [type, .meta 80 .type 4, .rigid 81 .region 4, .unit, .bottom,
   .scalar .character, .tuple [type, .reference .unique region type],
   .array type size, .reference .shared region type, .rawPointer .unique type,
   .named ["pkg", "Thing"] [type, region, size] .type,
   .nominal ⟨1, 20⟩ [type, size], .alias ⟨1, 21⟩ [type, region],
   .callable ⟨1, 22⟩ [type, row], .continuation 30 type type row,
   .label brand region type, .environment brand region, .available brand region,
   .bindings brand region [type, .array type size], .effect ⟨1, 23⟩ [type, size],
   .row [effect] [row], .projection ⟨1, 24⟩ ⟨1, 25⟩ [type, region] .type,
   .constant (.character 65), .constantTuple [size],
   .constantConstructor ⟨1, 26⟩ [type, size] [size], .staticRegion]

example :
    (carriers (.param 1 .type) (.param 2 .region) (.param 3 .constant)
      (.param 4 .effect) (.param 5 .row) (.param 6 .brand)).mapM (substitute 10 replacements) =
    .ok (carriers typeArg .staticRegion sizeArg effectArg rowArg brandArg) := by rfl

example : substitute 1 [(1, .staticRegion)] (.param 1 .type) =
    reject .kindMismatch "generic replacement has the wrong kind" := by rfl

example : substitute 10 [(2, .unit)] (.tuple [.reference .unique (.param 2 .region) .unit]) =
    reject .kindMismatch "generic replacement has the wrong kind" := by rfl

-- Lookup retains the first binding, including a first invalid binding.
example : substitute 1 [(1, typeArg), (1, .unit)] (.param 1 .type) = .ok typeArg := by rfl
example : substitute 1 [(1, .staticRegion), (1, .unit)] (.param 1 .type) =
    reject .kindMismatch "generic replacement has the wrong kind" := by rfl

-- Missing replacements are free parameters, not unknown evidence converted to unit.
example : substitute 1 replacements (.param 99 .row) = .ok (.param 99 .row) := by rfl
-- Substitution is simultaneous: replacement terms are not recursively substituted.
example : substitute 1 [(1, .param 2 .type), (2, .unit)] (.param 1 .type) =
    .ok (.param 2 .type) := by rfl
example : substitute 0 replacements .unit =
    reject .resourceLimit "substitution depth exhausted" := by rfl
example : substitute 1 replacements (.tuple [.param 1 .type]) =
    reject .resourceLimit "substitution depth exhausted" := by rfl

-- A real consumer cannot silently replace a lifetime with an ordinary type.
example : substituteConstraint 10 [(2, .unit)] (.outlives (.param 2 .region) .staticRegion) =
    reject .kindMismatch "generic replacement has the wrong kind" := by rfl

def signature : Signature :=
  { generics := [⟨1, "T", .type, none⟩, ⟨2, "r", .region, none⟩]
    arguments := [.reference .shared (.param 2 .region) (.param 1 .type)]
    output := .param 1 .type
    effects := .param 5 .row
    constraints := [.outlives (.param 2 .region) .staticRegion] }

example : substituteSignature 10 replacements signature =
    .ok { signature with
      generics := []
      arguments := [.reference .shared .staticRegion typeArg]
      output := typeArg
      effects := rowArg
      constraints := [.outlives .staticRegion .staticRegion] } := by rfl

example : substituteSignature 10 [(2, .unit)] signature =
    reject .kindMismatch "generic replacement has the wrong kind" := by rfl

-- A higher-ranked binder shadows replacements with the same identity.
example : substituteConstraint 10 [(2, .unit)]
    (.higherRanked [⟨2, "r", .region, none⟩] [.outlives (.param 2 .region) .staticRegion]) =
    .ok (.higherRanked [⟨2, "r", .region, none⟩] [.outlives (.param 2 .region) .staticRegion]) := by rfl

-- The guarantee is universally quantified, not just established for the fixtures above.
example (fuel : Nat) (arguments : Substitution) (before after : Term)
    (accepted : substitute fuel arguments before = .ok after) :
    Spec.Substitutes arguments before after ∧ before.kind = after.kind :=
  ⟨Spec.substitute_sound fuel arguments before after accepted,
    substitute_kind fuel arguments before after accepted⟩

#print axioms Spec.substitute_sound
#print axioms substitute_kind

end SubstitutionRegression
