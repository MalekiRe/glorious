import GloriousLanguage.RuntimeSignatureEquivariance

/-! Runtime-name transport through the complete lexical function body. The
single syntax action is shared by substitution and continuation relocation;
the source inventory, rather than an assumed instance-equivalence fact,
establishes that immutable templates contain no runtime identities. -/
namespace Glorious.Language

theorem Kernel.Pattern.terms_mapTerms (f : Term → Term) (pattern : Kernel.Pattern) :
    (pattern.mapTerms f).terms = pattern.terms.map f := by
  cases pattern <;> simp only [Kernel.Pattern.mapTerms,Kernel.Pattern.terms,Kernel.Local.mapTerms,
    List.map_cons,List.map_nil,List.flatMap_map,List.map_flatMap]
  all_goals first
  | exact Kernel.Pattern.terms_mapTerms f _
  | apply List.flatMap_congr_left
    intro child _
    exact child.terms_mapTerms f
termination_by pattern

theorem Kernel.Atom.terms_mapTerms (f : Term → Term) (atom : Kernel.Atom) :
    (atom.mapTerms f).terms = atom.terms.map f := by
  cases atom <;> simp only [Kernel.Atom.mapTerms,Kernel.Atom.terms,Kernel.Capture.mapTerms,
    List.map_cons,List.map_nil,List.map_append,List.map_map,Function.comp_def]

theorem Kernel.Invocation.terms_mapTerms (f : Term → Term) (call : Kernel.Invocation) :
    (call.mapTerms f).terms = call.terms.map f := by
  simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Kernel.Invocation.terms,
    Signature.terms_mapTerms,List.map_append,List.flatMap_map,List.map_flatMap,Option.toList_map,
    Kernel.EnvironmentAccess.mapTerms,List.map_cons,List.map_nil]

theorem Signature.mapTerms_id (signature : Signature) : signature.mapTerms id = signature := by
  simp only [Signature.mapTerms,List.map_id_fun,id_eq,Option.map_id_fun]
  congr 1
  · exact List.map_eq_self_of _ _ (fun binder _ => by cases binder; rfl)
  · exact List.map_eq_self_of _ _ (fun constraint _ => constraint.mapTerms_id)

theorem Signature.mapTerms_eq_self (f : Term → Term) (signature : Signature)
    (fixed : ∀ term ∈ signature.terms, f term = term) : signature.mapTerms f = signature :=
  (signature.mapTerms_congr f id fixed).trans signature.mapTerms_id

namespace Kernel

private theorem option_map_eq_self {α : Type} (f : α → α) (option : Option α)
    (fixed : ∀ value, option = some value → f value = value) : option.map f = option := by
  cases option with
  | none => rfl
  | some value => simp only [Option.map,fixed value rfl]

theorem Local.mapTerms_eq_self {f : Term → Term} {localSlot : Local} (fixed : f localSlot.type = localSlot.type) :
    localSlot.mapTerms f = localSlot := by
  cases localSlot
  simp only [Local.mapTerms] at fixed ⊢
  rw [fixed]

theorem Capture.mapTerms_eq_self {f : Term → Term} {capture : Capture} (fixed : f capture.type = capture.type) :
    capture.mapTerms f = capture := by
  cases capture
  simp only [Capture.mapTerms] at fixed ⊢
  rw [fixed]

theorem Local.mapTerms_comp (first second : Term → Term) (localSlot : Local) :
    (localSlot.mapTerms first).mapTerms second = localSlot.mapTerms (second ∘ first) := rfl

theorem Capture.mapTerms_comp (first second : Term → Term) (capture : Capture) :
    (capture.mapTerms first).mapTerms second = capture.mapTerms (second ∘ first) := rfl

theorem Pattern.mapTerms_comp (first second : Term → Term) (pattern : Pattern) :
    (pattern.mapTerms first).mapTerms second = pattern.mapTerms (second ∘ first) := by
  cases pattern <;> simp only [Pattern.mapTerms,Local.mapTerms_comp,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | exact Pattern.mapTerms_comp first second _
    | apply List.map_congr_left
      intro field _
      exact field.mapTerms_comp first second
termination_by pattern

theorem Atom.mapTerms_comp (first second : Term → Term) (atom : Atom) :
    (atom.mapTerms first).mapTerms second = atom.mapTerms (second ∘ first) := by
  cases atom <;> simp only [Atom.mapTerms,List.map_map,Function.comp_def,Capture.mapTerms_comp]

theorem EnvironmentAccess.mapTerms_comp (first second : Term → Term) (access : EnvironmentAccess) :
    (access.mapTerms first).mapTerms second = access.mapTerms (second ∘ first) := rfl

theorem Invocation.transformTerms_comp (first second : Term → Term)
    (firstSignatures secondSignatures : Signature → Signature) (call : Invocation) :
    (call.transformTerms first firstSignatures).transformTerms second secondSignatures =
      call.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
  simp only [Invocation.transformTerms,Option.map_map,Function.comp_def,EnvironmentAccess.mapTerms_comp]

mutual
  theorem Code.transformTerms_comp (first second : Term → Term)
      (firstSignatures secondSignatures : Signature → Signature) (code : Code) :
      (code.transformTerms first firstSignatures).transformTerms second secondSignatures =
        code.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
    cases code <;> simp only [Code.transformTerms,Local.mapTerms_comp,Atom.mapTerms_comp,
      Invocation.transformTerms_comp,Pattern.mapTerms_comp,List.map_map,Function.comp_def]
    all_goals try rfl
    all_goals
      congr 1
      all_goals first
      | exact Code.transformTerms_comp first second firstSignatures secondSignatures _
      | exact Handler.transformTerms_comp first second firstSignatures secondSignatures _
      | apply List.map_congr_left
        intro arm _
        exact arm.transformTerms_comp first second firstSignatures secondSignatures
  termination_by sizeOf code

  theorem Arm.transformTerms_comp (first second : Term → Term)
      (firstSignatures secondSignatures : Signature → Signature) (arm : Arm) :
      (arm.transformTerms first firstSignatures).transformTerms second secondSignatures =
        arm.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
    cases arm
    simp only [Arm.transformTerms,Pattern.mapTerms_comp]
    congr 1
    exact Code.transformTerms_comp first second firstSignatures secondSignatures _
  termination_by sizeOf arm

  theorem OperationArm.transformTerms_comp (first second : Term → Term)
      (firstSignatures secondSignatures : Signature → Signature) (arm : OperationArm) :
      (arm.transformTerms first firstSignatures).transformTerms second secondSignatures =
        arm.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
    cases arm
    simp only [OperationArm.transformTerms,List.map_map,Function.comp_def,Option.map_map,
      Pattern.mapTerms_comp,Local.mapTerms_comp]
    congr 1
    exact Code.transformTerms_comp first second firstSignatures secondSignatures _
  termination_by sizeOf arm

  theorem Handler.transformTerms_comp (first second : Term → Term)
      (firstSignatures secondSignatures : Signature → Signature) (handler : Handler) :
      (handler.transformTerms first firstSignatures).transformTerms second secondSignatures =
        handler.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
    cases handler
    simp only [Handler.transformTerms,List.map_map,Function.comp_def,Capture.mapTerms_comp]
    congr 1
    all_goals
      apply List.map_congr_left
      intro arm _
      exact arm.transformTerms_comp first second firstSignatures secondSignatures
  termination_by sizeOf handler
end

theorem Function.transformTerms_comp (first second : Term → Term)
    (firstSignatures secondSignatures : Signature → Signature) (function : Function) :
    (function.transformTerms first firstSignatures).transformTerms second secondSignatures =
      function.transformTerms (second ∘ first) (secondSignatures ∘ firstSignatures) := by
  simp only [Function.transformTerms,List.map_map,Function.comp_def,Local.mapTerms_comp,Code.transformTerms_comp]

theorem Invocation.mapTerms_comp (first second : Term → Term) (call : Invocation) :
    (call.mapTerms first).mapTerms second = call.mapTerms (second ∘ first) := by
  simp only [Invocation.mapTerms,Invocation.transformTerms_comp]
  exact congrArg (Invocation.transformTerms _ · call) (funext (fun signature => signature.mapTerms_comp first second))

theorem Code.mapTerms_comp (first second : Term → Term) (code : Code) :
    (code.mapTerms first).mapTerms second = code.mapTerms (second ∘ first) := by
  simp only [Code.mapTerms,Code.transformTerms_comp]
  exact congrArg (Code.transformTerms _ · code) (funext (fun signature => signature.mapTerms_comp first second))

theorem Function.mapTerms_comp (first second : Term → Term) (function : Function) :
    (function.mapTerms first).mapTerms second = function.mapTerms (second ∘ first) := by
  simp only [Function.mapTerms,Function.transformTerms_comp]
  exact congrArg (Function.transformTerms _ · function) (funext (fun signature => signature.mapTerms_comp first second))

theorem Pattern.mapTerms_eq_self (f : Term → Term) (pattern : Pattern)
    (fixed : ∀ term ∈ pattern.terms, f term = term) : pattern.mapTerms f = pattern := by
  cases pattern <;> simp only [Pattern.mapTerms]
  all_goals try rfl
  case bind =>
    congr 1
    exact Local.mapTerms_eq_self (fixed _ (by simp [Pattern.terms]))
  case reference =>
    congr 1
    exact Pattern.mapTerms_eq_self f _ (by simpa only [Pattern.terms] using fixed)
  all_goals
    congr 1
    all_goals first
    | apply List.map_eq_self_of
      intro field member
      exact field.mapTerms_eq_self f (fun term present => fixed term (by
        simp only [Pattern.terms,List.mem_flatMap]
        exact ⟨field,member,present⟩))
termination_by pattern

theorem Atom.mapTerms_eq_self (f : Term → Term) (atom : Atom)
    (fixed : ∀ term ∈ atom.terms, f term = term) : atom.mapTerms f = atom := by
  cases atom <;> simp only [Atom.mapTerms]
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | exact fixed _ (by simp [Atom.terms])
    | apply List.map_eq_self_of
      intro term member
      exact fixed term (by simp [Atom.terms,member])
    | apply List.map_eq_self_of
      intro capture member
      exact Capture.mapTerms_eq_self (fixed _ (by
        simp only [Atom.terms,List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨capture,member,rfl⟩)))

theorem Invocation.mapTerms_eq_self (f : Term → Term) (call : Invocation)
    (fixed : ∀ term ∈ call.terms, f term = term) : call.mapTerms f = call := by
  have signature := call.signature.mapTerms_eq_self f (fun term member => fixed term (by simp [Invocation.terms,member]))
  cases call with
  | mk callee arguments receiver environment callSignature =>
      simp only [Invocation.mapTerms,Invocation.transformTerms]
      congr 1
      · apply option_map_eq_self
        intro access found
        cases access with
        | mk witness mode region after =>
          simp only [EnvironmentAccess.mapTerms]
          congr 1
          all_goals apply fixed; simp only [Invocation.terms,List.mem_append]; right
          all_goals exact List.mem_flatMap.mpr ⟨⟨witness,mode,region,after⟩,Option.mem_toList.mpr found,by simp⟩
mutual
  theorem Code.mapTerms_eq_self (f : Term → Term) (code : Code)
      (fixed : ∀ term ∈ code.terms, f term = term) : code.mapTerms f = code := by
    cases code <;> simp only [Code.mapTerms,Code.transformTerms]
    all_goals try rfl
    all_goals
      congr 1
      all_goals first
      | exact Local.mapTerms_eq_self (fixed _ (by simp [Code.terms]))
      | exact Atom.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Code.terms,member]))
      | exact Pattern.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Code.terms,member]))
      | exact Invocation.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Code.terms,member]))
      | exact Code.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Code.terms,member]))
      | exact Handler.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Code.terms,member]))
      | exact fixed _ (by simp [Code.terms])
      | apply List.map_eq_self_of
        intro arm member
        exact arm.mapTerms_eq_self f (fun term present => fixed term (by
          simp only [Code.terms,List.mem_flatMap]
          exact ⟨arm,member,present⟩))
  termination_by sizeOf code

  theorem Arm.mapTerms_eq_self (f : Term → Term) (arm : Arm)
      (fixed : ∀ term ∈ arm.terms, f term = term) : arm.mapTerms f = arm := by
    cases arm
    simp only [Arm.mapTerms,Arm.transformTerms]
    congr 1
    · exact Pattern.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Arm.terms,member]))
    · exact Code.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Arm.terms,member]))
  termination_by sizeOf arm

  theorem OperationArm.mapTerms_eq_self (f : Term → Term) (arm : OperationArm)
      (fixed : ∀ term ∈ arm.terms, f term = term) : arm.mapTerms f = arm := by
    cases arm
    simp only [OperationArm.mapTerms,OperationArm.transformTerms]
    congr 1
    · exact List.map_eq_self_of _ _ (fun term member => fixed term (by simp [OperationArm.terms,member]))
    · exact List.map_eq_self_of _ _ (fun term member => fixed term (by simp [OperationArm.terms,member]))
    · apply List.map_eq_self_of
      intro pattern member
      exact pattern.mapTerms_eq_self f (fun term present => fixed term (by
        simp only [OperationArm.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨pattern,member,present⟩)))))
    · apply option_map_eq_self
      intro localSlot found
      exact Local.mapTerms_eq_self (fixed _ (by
        simp only [OperationArm.terms,List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨localSlot,Option.mem_toList.mpr found,rfl⟩))))
    · exact Code.mapTerms_eq_self f _ (fun term member => fixed term (by simp [OperationArm.terms,member]))
  termination_by sizeOf arm

  theorem Handler.mapTerms_eq_self (f : Term → Term) (handler : Handler)
      (fixed : ∀ term ∈ handler.terms, f term = term) : handler.mapTerms f = handler := by
    cases handler
    simp only [Handler.mapTerms,Handler.transformTerms]
    congr 1
    · exact fixed _ (by simp [Handler.terms])
    · apply List.map_eq_self_of
      intro arm member
      exact arm.mapTerms_eq_self f (fun term present => fixed term (by
        simp only [Handler.terms,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨arm,member,present⟩)))))
    · apply List.map_eq_self_of
      intro arm member
      exact arm.mapTerms_eq_self f (fun term present => fixed term (by
        simp only [Handler.terms,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨arm,member,present⟩)))))
    · apply List.map_eq_self_of
      intro capture member
      exact Capture.mapTerms_eq_self (fixed _ (by
        simp only [Handler.terms,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨capture,member,rfl⟩))))
  termination_by sizeOf handler
end

theorem Function.mapTerms_eq_self (f : Term → Term) (function : Function)
    (fixed : ∀ term ∈ function.terms, f term = term) : function.mapTerms f = function := by
  cases function
  simp only [Function.mapTerms,Function.transformTerms]
  congr 1
  · apply List.map_eq_self_of
    intro localSlot member
    exact Local.mapTerms_eq_self (fixed _ (by
      simp only [Function.terms,List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨localSlot,member,rfl⟩)))))
  · apply List.map_eq_self_of
    intro capture member
    exact Local.mapTerms_eq_self (fixed _ (by
      simp only [Function.terms,List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨capture,member,rfl⟩))))
  · exact Signature.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Function.terms,member]))
  · exact Code.mapTerms_eq_self f _ (fun term member => fixed term (by simp [Function.terms,member]))

theorem BodyInventory.lexical {program : Program} (inventory : BodyInventory program)
    {function : Function} (member : function ∈ program.functions) : function.Lexical :=
  inventory.2.2.2 function member

end Kernel

def RegionPermutation.code (permutation : RegionPermutation) : Kernel.Code → Kernel.Code :=
  Kernel.Code.mapTerms permutation.term

def RegionPermutation.function (permutation : RegionPermutation) : Kernel.Function → Kernel.Function :=
  Kernel.Function.mapTerms permutation.term

theorem RegionPermutation.code_instantiate (permutation : RegionPermutation)
    (code : Kernel.Code) (substitution : Substitution) :
    permutation.code (code.instantiate substitution) =
      (permutation.code code).instantiate (permutation.substitution substitution) := by
  simp only [RegionPermutation.code,Kernel.Code.mapTerms,Kernel.Code.instantiate,Kernel.Code.transformTerms_comp]
  congr 1
  · exact funext (fun term => permutation.term_substitute substitution term)
  · exact funext (fun signature => permutation.signature_instantiate signature substitution)

theorem Kernel.Function.mapTerms_instantiate (f : Term → Term) (mapped : Substitution → Substitution)
    (terms : ∀ substitution term, f (term.substitute substitution) = (f term).substitute (mapped substitution))
    (filtered : ∀ substitution (keep : Identity → Bool), mapped (substitution.filter (fun entry => keep entry.1)) =
      (mapped substitution).filter (fun entry => keep entry.1))
    (function : Kernel.Function) (substitution : Substitution) :
    (function.instantiate substitution).mapTerms f = (function.mapTerms f).instantiate (mapped substitution) := by
  simp only [Kernel.Function.mapTerms,Kernel.Function.instantiate,Kernel.Function.transformTerms_comp]
  congr 1
  · exact funext (terms substitution)
  · exact funext (fun signature => signature.mapTerms_instantiate f mapped terms filtered substitution)

theorem RegionPermutation.function_instantiate (permutation : RegionPermutation)
    (function : Kernel.Function) (substitution : Substitution) :
    permutation.function (function.instantiate substitution) =
      (permutation.function function).instantiate (permutation.substitution substitution) :=
  function.mapTerms_instantiate permutation.term permutation.substitution permutation.term_substitute permutation.substitution_filter substitution

theorem RegionPermutation.lexical_function (permutation : RegionPermutation) {function : Kernel.Function}
    (lexical : function.Lexical) : permutation.function function = function :=
  function.mapTerms_eq_self permutation.term (fun term member => permutation.lexical_term (lexical term member))

/-- The checked immutable body template produces the exact transported
instance, not just a callable with equal capture-field types. -/
theorem Kernel.Instance.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (selected : Kernel.Instance program id arguments function) (permutation : RegionPermutation) :
    Kernel.Instance program id (arguments.map permutation.term) (permutation.function function) := by
  rcases selected with ⟨template,declaration,substitution,body,signature,agrees,instantiated,requirements,closed,rfl⟩
  have templateLexical := inventory.lexical (List.mem_of_find?_eq_some body)
  have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup signature))
  have constraints : ∀ constraint ∈ template.signature.constraints, ∀ term ∈ constraint.terms, term.Lexical := by
    intro constraint member term present
    apply lexical term
    simp only [Definition.terms,List.mem_append]
    apply Or.inl; apply Or.inl
    rw [agrees] at member
    simp only [Signature.terms,List.mem_append,List.mem_cons]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨constraint,member,present⟩))
  refine ⟨template,declaration,permutation.substitution substitution,body,signature,agrees,
    instantiated.permute permutation,?_,?_,?_⟩
  · simpa only [RegionPermutation.context,List.map_nil] using requirements.permute valid constraints permutation
  · intro argument member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact (closed original present).permute permutation
  · rw [permutation.function_instantiate,permutation.lexical_function templateLexical]

theorem Execution.Relocation.substitution_filter (map : Execution.Relocation) (substitution : Substitution)
    (keep : Identity → Bool) : map.substitution (substitution.filter (fun entry => keep entry.1)) =
      (map.substitution substitution).filter (fun entry => keep entry.1) := by
  simp only [Execution.Relocation.substitution,List.filter_map,Function.comp_def]

/-- Argument agreement determines the entire checked instantiated body. No
independent reconstruction of a body's runtime-name support is necessary. -/
theorem Kernel.Instance.relocation_permutation {program : Kernel.Program} (inventory : Kernel.BodyInventory program)
    {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (selected : Kernel.Instance program id arguments function) (map : Execution.Relocation) (permutation : RegionPermutation)
    (argumentsAgree : ∀ argument ∈ arguments, map.term argument = permutation.term argument) :
    function.mapTerms map.term = permutation.function function := by
  obtain ⟨template,declaration,substitution,found,_,_,instantiated,_,_,rfl⟩ := selected
  have lexical := inventory.lexical (List.mem_of_find?_eq_some found)
  have fixed : template.mapTerms map.term = template :=
    template.mapTerms_eq_self map.term (fun term member => map.lexical_term term (lexical term member))
  have substitutionAgree : map.substitution substitution = permutation.substitution substitution := by
    simp only [Execution.Relocation.substitution,RegionPermutation.substitution]
    apply List.map_congr_left
    intro entry member
    rw [instantiated.2.2] at member
    exact congrArg (fun term => (entry.1,term)) (argumentsAgree entry.2 (List.of_mem_zip member).2)
  rw [template.mapTerms_instantiate map.term map.substitution map.term_substitute map.substitution_filter,
    fixed,permutation.function_instantiate,permutation.lexical_function lexical,substitutionAgree]

end Glorious.Language
