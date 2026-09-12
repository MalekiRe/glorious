import GloriousLanguage.RuntimeCodeEquivariance

/-! Structural typing transport for the complete code action. Runtime
coverage obligations remain semantic judgments over actual typed storage;
their eventual transport must use the same world and matching semantics. -/
namespace Glorious.Language

theorem RegionPermutation.code_involutive (permutation : RegionPermutation) (code : Kernel.Code) :
    permutation.code (permutation.code code) = code := by
  simp only [RegionPermutation.code,Kernel.Code.mapTerms_comp]
  exact code.mapTerms_eq_self _ (fun term _ => permutation.term_involutive term)

theorem RegionPermutation.function_involutive (permutation : RegionPermutation) (function : Kernel.Function) :
    permutation.function (permutation.function function) = function := by
  simp only [RegionPermutation.function,Kernel.Function.mapTerms_comp]
  exact function.mapTerms_eq_self _ (fun term _ => permutation.term_involutive term)

theorem RegionPermutation.substitution_append (permutation : RegionPermutation) (first second : Substitution) :
    permutation.substitution (first ++ second) = permutation.substitution first ++ permutation.substitution second := by
  simp only [RegionPermutation.substitution,List.map_append]


theorem DomainValid.permute {program : Program} (valid : ProgramWellFormed program) {context : Context} {term : Term}
    (domain : DomainValid program context term) (permutation : RegionPermutation) :
    DomainValid program (permutation.context context) (permutation.term term) := by
  refine ⟨?_,?_,?_⟩
  · intro id arguments data substitution occurs found instantiated
    have original := permutation.occurs occurs
    rw [permutation.term_involutive] at original
    simp only [RegionPermutation.term,Term.renameRuntimeRegions] at original
    have requirements := domain.1 id (arguments.map permutation.term) data (permutation.substitution substitution)
      original found (instantiated.permute permutation)
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    have transported := requirements.permute valid (fun requirement member term present => lexical term (by
      have nested : term ∈ data.requirements.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨requirement,member,present⟩
      simp only [Definition.terms,List.mem_append,nested,or_true,true_or])) permutation
    simpa only [permutation.substitution_involutive] using transported
  · intro id arguments effect substitution occurs found instantiated
    have original := permutation.occurs occurs
    rw [permutation.term_involutive] at original
    simp only [RegionPermutation.term,Term.renameRuntimeRegions] at original
    have requirements := domain.2.1 id (arguments.map permutation.term) effect (permutation.substitution substitution)
      original found (instantiated.permute permutation)
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.effect_lookup found))
    have transported := requirements.permute valid (fun requirement member term present => lexical term (by
      have nested : term ∈ effect.requirements.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨requirement,member,present⟩
      simp only [Definition.terms,List.mem_append,nested,true_or])) permutation
    simpa only [permutation.substitution_involutive] using transported
  · intro trait member owners items declaration associated ownerSub itemSub occurs found selected ownerInst itemInst
    have original := permutation.occurs occurs
    rw [permutation.term_involutive] at original
    simp only [RegionPermutation.term,Term.renameRuntimeRegions] at original
    have requirements := domain.2.2 trait member (owners.map permutation.term) (items.map permutation.term)
      declaration associated (permutation.substitution ownerSub) (permutation.substitution itemSub)
      original found selected (ownerInst.permute permutation) (itemInst.permute permutation)
    have declarationLexical := valid.lexical (List.mem_of_find?_eq_some (Program.trait_lookup found))
    have associatedLexical := valid.lexical (List.mem_of_find?_eq_some (Program.associated_lookup selected))
    have ownerRequirements := requirements.1.permute valid (fun requirement present term nested => declarationLexical term (by
      have occurs : term ∈ declaration.requirements.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨requirement,present,nested⟩
      simp only [Definition.terms,List.mem_append,occurs,true_or])) permutation
    have itemRequirements := requirements.2.permute valid (fun requirement present term nested => associatedLexical term (by
      have occurs : term ∈ associated.requirements.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨requirement,present,nested⟩
      simp only [Definition.terms,List.mem_append,occurs,or_true,true_or])) permutation
    exact ⟨by simpa only [permutation.substitution_involutive] using ownerRequirements,
      by simpa only [permutation.substitution_append,permutation.substitution_involutive] using itemRequirements⟩

theorem WellKinded.permute {program : Program} (valid : ProgramWellFormed program) {context : Context} {term : Term} {kind : Kind}
    (kinded : WellKinded program context term kind) (permutation : RegionPermutation) :
    WellKinded program (permutation.context context) (permutation.term term) kind :=
  ⟨kinded.1.permute permutation,kinded.2.permute valid permutation⟩

theorem Subtype.permute {program : Program} (valid : ProgramWellFormed program) {context : Context} {first second : Term}
    (subtype : Subtype program context first second) (permutation : RegionPermutation) :
    Subtype program (permutation.context context) (permutation.term first) (permutation.term second) := by
  refine Subtype.rec
    (motive_1 := fun first second _ => Subtype program (permutation.context context) (permutation.term first) (permutation.term second))
    (motive_2 := fun data parameter first second _ =>
      VarianceSubtype program (permutation.context context) data parameter (permutation.term first) (permutation.term second))
    (motive_3 := fun first second _ =>
      ListRel (Subtype program (permutation.context context)) (first.map permutation.term) (second.map permutation.term))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ subtype
  all_goals simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  · intro a b equal
    exact .equal (equal.permute valid permutation)
  · intro type kinded
    exact .bottom (kinded.permute valid permutation)
  · intro long short a b included _ ih
    exact .shared (by simpa only [RegionPermutation.constraint,Constraint.mapTerms,RegionPermutation.term]
      using included.permute valid permutation) ih
  · intro long short a b included equal
    exact .unique (by simpa only [RegionPermutation.constraint,Constraint.mapTerms,RegionPermutation.term]
      using included.permute valid permutation) (equal.permute valid permutation)
  · intro a b _ fields
    exact .tuple fields
  · intro a b n m _ equal ih
    exact .array ih (equal.permute valid permutation)
  · intro id data a b found length aligned _ fields
    refine .nominal found (by simpa only [List.length_map] using length)
      (by simpa only [List.length_map] using aligned) ?_
    intro index binder x y atBinder atX atY
    rw [List.getElem?_map] at atX atY
    obtain ⟨oldX,firstAt,rfl⟩ := Option.map_eq_some_iff.mp atX
    obtain ⟨oldY,secondAt,rfl⟩ := Option.map_eq_some_iff.mp atY
    exact fields index binder oldX oldY atBinder firstAt secondAt
  · intro data parameter a b equal
    exact .equal (equal.permute valid permutation)
  · intro data parameter a b variance _ ih
    exact .covariant variance ih
  · intro data parameter a b variance _ ih
    exact .contravariant variance ih
  · intro data parameter a b variance
    exact .unused variance
  · exact .nil
  · intro a b as bs _ _ first rest
    exact .cons first rest

theorem ConstantType.permute {program : Program} (valid : ProgramWellFormed program) {context : Context} {value type : Term}
    (typed : ConstantType program context value type) (permutation : RegionPermutation) :
    ConstantType program (permutation.context context) (permutation.term value) (permutation.term type) := by
  refine ConstantType.rec
    (motive_1 := fun value type _ => ConstantType program (permutation.context context) (permutation.term value) (permutation.term type))
    (motive_2 := fun values types _ => ListRel (ConstantType program (permutation.context context))
      (values.map permutation.term) (types.map permutation.term))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  · intro value valid
    exact .scalar valid
  · exact .unit
  · intro fields types _ constants
    exact .tuple constants
  · intro constructor data variant arguments values substitution types found instantiated kinded substituted _ constants
    refine .constructor found (instantiated.permute permutation) ?_ ?_ constants
    · intro argument member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change Kinding program (permutation.context context) (permutation.term original) (permutation.term original).kind
      simpa only [permutation.term_kind] using (kinded original present).permute permutation
    apply permutation.substitutes_lexical_list _ substituted
    intro type member
    obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
    exact valid.field_lexical found.1 found.2.1 inFields
  · intro value a b _ equal ih
    exact .equal ih (equal.permute valid permutation)
  · exact .nil
  · intro a b as bs _ _ first rest
    exact .cons first rest

theorem Addressable.permute {program : Program} (valid : ProgramWellFormed program) {context : Context} {type : Term}
    (addressable : Addressable program context type) (permutation : RegionPermutation) :
    Addressable program (permutation.context context) (permutation.term type) := by
  induction addressable <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  all_goals first
  | exact .unit
  | exact .scalar
  | exact .tuple
  | exact .array
  | exact .nominal
  | exact .reference
  | exact .pointer
  | exact .callable
  | exact .continuation
  | exact .bindings
  | skip
  case equal equal _ ih => exact .equal (equal.permute valid permutation) ih

def RegionPermutation.typingContext (permutation : RegionPermutation) (context : Typing.Context) : Typing.Context :=
  { context with
    static := permutation.context context.static
    locals := context.locals.map (Kernel.Local.mapTerms permutation.term)
    labels := context.labels.map (fun (id,region,type) => (id,permutation.term region,permutation.term type))
    effects := permutation.term context.effects
    environment := context.environment.map permutation.term }

theorem RegionPermutation.typingContext_bind (permutation : RegionPermutation) (context : Typing.Context) (localSlot : Kernel.Local) :
    permutation.typingContext (context.bind localSlot) =
      (permutation.typingContext context).bind (localSlot.mapTerms permutation.term) := by
  simp only [RegionPermutation.typingContext,Typing.Context.bind,List.map_cons,List.filter_map,Function.comp_def,Kernel.Local.mapTerms]

theorem Typing.FieldType.permute {program : Program} (valid : ProgramWellFormed program) {context : Language.Context}
    {type field : Term} {index : Nat} {visible : Bool} (located : Typing.FieldType program context type index field visible)
    (permutation : RegionPermutation) :
    Typing.FieldType program (permutation.context context) (permutation.term type) index (permutation.term field) visible := by
  rcases located with ⟨fields,rfl,selected⟩ | ⟨element,length,rfl,rfl⟩ |
    ⟨id,arguments,data,variant,substitution,types,rfl,found,notEnum,variants,instantiated,substituted,selected,visibility⟩
  · refine Or.inl ⟨fields.map permutation.term,?_,?_⟩
    · simp only [RegionPermutation.term,Term.renameRuntimeRegions]
    · rw [List.getElem?_map,selected]; rfl
  · refine Or.inr (Or.inl ⟨permutation.term field,permutation.term length,?_,rfl⟩)
    simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  · have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine Or.inr (Or.inr ⟨id,arguments.map permutation.term,data,variant,permutation.substitution substitution,
      types.map permutation.term,?_,found,notEnum,variants,instantiated.permute permutation,?_,?_,visibility⟩)
    · simp only [RegionPermutation.term,Term.renameRuntimeRegions]
    · apply permutation.substitutes_lexical_list _ substituted
      intro type member
      obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
      exact lexical field.type (by
        simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl ⟨field,⟨variant,by rw [variants]; simp,inFields⟩,rfl⟩)))
    · rw [List.getElem?_map,selected]; rfl

theorem Typing.Projections.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {type result : Term} {mutable writable : Bool} {projections : List Kernel.Projection}
    (projected : Typing.Projections program context type mutable projections result writable) (permutation : RegionPermutation) :
    Typing.Projections program (permutation.typingContext context) (permutation.term type) mutable projections (permutation.term result) writable := by
  induction projected <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions]
  case nil => exact .nil
  case field located _ ih => exact .field (located.permute valid permutation) ih
  case index indexed _ ih =>
    obtain ⟨binding,member,identity,type⟩ := indexed
    exact .index ⟨binding.mapTerms permutation.term,List.mem_map.mpr ⟨binding,member,rfl⟩,identity,
      by simp only [Kernel.Local.mapTerms,type,RegionPermutation.term,Term.renameRuntimeRegions]⟩ ih
  case dereference _ ih => exact .dereference ih
  case equal equal _ ih => exact .equal (equal.permute valid permutation) ih

theorem Typing.PlaceType.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {place : Kernel.Place} {type : Term} {writable : Bool} (typed : Typing.PlaceType program context place type writable)
    (permutation : RegionPermutation) :
    Typing.PlaceType program (permutation.typingContext context) place (permutation.term type) writable := by
  obtain ⟨localSlot,member,identity,projected⟩ := typed
  exact ⟨localSlot.mapTerms permutation.term,List.mem_map.mpr ⟨localSlot,member,rfl⟩,identity,projected.permute valid permutation⟩

theorem Typing.PlacesType.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {places : List Kernel.Place} {types : List Term} (typed : Typing.PlacesType program context places types)
    (permutation : RegionPermutation) :
    Typing.PlacesType program (permutation.typingContext context) places (types.map permutation.term) := by
  induction typed with
  | nil => exact .nil
  | cons first _ ih =>
    obtain ⟨actual,writable,located,subtype⟩ := first
    exact .cons ⟨permutation.term actual,writable,located.permute valid permutation,subtype.permute valid permutation⟩ ih

theorem RegionPermutation.access_type (permutation : RegionPermutation) (access : Access) (region type : Term) :
    permutation.term (access.type region type) = access.type (permutation.term region) (permutation.term type) := by
  cases access <;> simp only [Access.type,RegionPermutation.term,Term.renameRuntimeRegions]

theorem Kernel.RunsInEnvironment.permute {program : Language.Program} (valid : ProgramWellFormed program) {context : Language.Context}
    {call : Kernel.Invocation} {receiver brand region : Term} {residents : List Term}
    (runs : Kernel.RunsInEnvironment program context call receiver brand region residents) (permutation : RegionPermutation) :
    Kernel.RunsInEnvironment program (permutation.context context) (call.mapTerms permutation.term)
      (permutation.term receiver) (permutation.term brand) (permutation.term region) (residents.map permutation.term) := by
  obtain ⟨selected,environment,kinded,included,callable,runs,after⟩ := runs
  refine ⟨selected.mapTerms permutation.term,?_,kinded.permute valid permutation,
    by simpa only [RegionPermutation.constraint,Constraint.mapTerms,EnvironmentAccess.mapTerms]
      using included.permute valid permutation,?_,?_,?_⟩
  · simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,environment,Option.map]
  · simpa only [RegionPermutation.constraint,Constraint.mapTerms,permutation.access_type,
      Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Signature.mapTerms,Kernel.EnvironmentAccess.mapTerms]
      using callable.permute valid permutation
  · have transported := runs.permute valid permutation
    simp only [RegionPermutation.constraint,Constraint.mapTerms,permutation.access_type] at transported
    simpa only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Signature.mapTerms,Kernel.EnvironmentAccess.mapTerms,
      RegionPermutation.term,Term.renameRuntimeRegions] using transported
  · intro notOwned
    have equality := congrArg permutation.term (after notOwned)
    simpa only [Kernel.EnvironmentAccess.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions] using equality

theorem Typing.InvocationEnvironment.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {call : Kernel.Invocation} {receiver : Term} (environment : Typing.InvocationEnvironment program context call receiver)
    (permutation : RegionPermutation) :
    Typing.InvocationEnvironment program (permutation.typingContext context) (call.mapTerms permutation.term) (permutation.term receiver) := by
  rcases environment with none | ⟨selected,brand,region,residents,writable,found,located,runs⟩
  · exact Or.inl (by simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,none,Option.map])
  · refine Or.inr ⟨selected.mapTerms permutation.term,permutation.term brand,permutation.term region,
      residents.map permutation.term,writable,?_,?_,runs.permute valid permutation⟩
    · simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,found,Option.map]
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,Kernel.EnvironmentAccess.mapTerms] using located.permute valid permutation

theorem Typing.InvocationType.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {call : Kernel.Invocation} (typed : Typing.InvocationType program context call) (permutation : RegionPermutation) :
    Typing.InvocationType program (permutation.typingContext context) (call.mapTerms permutation.term) := by
  cases typed with
  | function located environment selected signature arguments safety effects writable =>
    refine .function ?_ ?_ (selected.permute valid permutation) ?_
      (arguments.permute valid permutation) safety (effects.permute valid permutation) writable
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms] using located.permute valid permutation
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using environment.permute valid permutation
    · exact congrArg permutation.signature signature
  | continuation environment located parameters result effects arguments allowed =>
    rename_i brand argument answer effectRow quantity writable
    refine .continuation (brand := permutation.term brand) (argument := permutation.term argument)
      (answer := permutation.term answer) (quantity := quantity) (writable := writable)
      ?_ ?_ ?_ ?_ ?_ ?_ (allowed.permute valid permutation)
    · simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,environment,Option.map]
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms] using located.permute valid permutation
    · simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Signature.mapTerms,parameters,List.map_cons,List.map_nil]
    · exact congrArg permutation.term result
    · exact congrArg permutation.term effects
    · simpa only [List.map_cons,List.map_nil,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms] using arguments.permute valid permutation
  | label environment located arguments result effects =>
    rename_i brand region resultType writable
    refine .label (brand := permutation.term brand) (region := permutation.term region)
      (result := permutation.term resultType) (writable := writable) ?_ ?_ ?_ ?_ ?_
    · simp only [Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,environment,Option.map]
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms] using located.permute valid permutation
    · simpa only [List.map_cons,List.map_nil,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms] using arguments.permute valid permutation
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Signature.mapTerms] using congrArg permutation.term result
    · simpa only [RegionPermutation.term,Term.renameRuntimeRegions,List.map_nil,Kernel.Invocation.mapTerms,Kernel.Invocation.transformTerms,Signature.mapTerms] using congrArg permutation.term effects

theorem Typing.PatternType.permute {program : Program} (valid : ProgramWellFormed program) {context : Language.Context}
    {pattern : Kernel.Pattern} {type : Term} {access : Access} {bindings : List Kernel.Local}
    (typed : Typing.PatternType program context pattern type access bindings) (permutation : RegionPermutation) :
    Typing.PatternType program (permutation.context context) (pattern.mapTerms permutation.term)
      (permutation.term type) access (bindings.map (Kernel.Local.mapTerms permutation.term)) := by
  refine Typing.PatternType.rec
    (motive_1 := fun pattern type access bindings _ => Typing.PatternType program (permutation.context context)
      (pattern.mapTerms permutation.term) (permutation.term type) access (bindings.map (Kernel.Local.mapTerms permutation.term)))
    (motive_2 := fun patterns types access bindings _ => Typing.PatternsType program (permutation.context context)
      (patterns.map (Kernel.Pattern.mapTerms permutation.term)) (types.map permutation.term) access
      (bindings.map (Kernel.Local.mapTerms permutation.term)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals simp only [Kernel.Pattern.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions,List.map_nil,List.map_cons,List.map_append]
  · intro type access
    exact .wildcard
  · intro localSlot type admitted equal
    exact .bind (admitted.permute permutation) (equal.permute valid permutation)
  · intro localSlot type mode region shape kinded
    refine .borrowBind ?_ (kinded.permute permutation)
    simpa only [Kernel.Local.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions] using congrArg permutation.term shape
  · intro scalar access bounded finite
    exact .scalar bounded finite
  · intro access
    exact .unit
  · intro patterns types access bindings _ ih
    exact .tuple ih
  · intro patterns type sign width count access bindings countEq _ ih
    refine .array (by simpa only [List.length_map] using countEq) ?_
    simpa only [List.map_replicate,List.length_map] using ih
  · intro id data variant arguments substitution types patterns access bindings found visible instantiated substituted _ owned ih
    refine .constructor found visible (instantiated.permute permutation) ?_ ih owned
    apply permutation.substitutes_lexical_list _ substituted
    intro type member
    obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
    exact valid.field_lexical found.1 found.2.1 inFields
  · intro mode region type pattern access bindings _ ih
    exact .reference ih
  · intro access
    exact .nil
  · intro pattern patterns type types access bindings more _ _ first rest
    exact .cons first rest

theorem Typing.PatternsType.permute {program : Program} (valid : ProgramWellFormed program) {context : Language.Context}
    {patterns : List Kernel.Pattern} {types : List Term} {access : Access} {bindings : List Kernel.Local}
    (typed : Typing.PatternsType program context patterns types access bindings) (permutation : RegionPermutation) :
    Typing.PatternsType program (permutation.context context) (patterns.map (Kernel.Pattern.mapTerms permutation.term))
      (types.map permutation.term) access (bindings.map (Kernel.Local.mapTerms permutation.term)) := by
  have whole := (Typing.PatternType.tuple typed).permute valid permutation
  simp only [Kernel.Pattern.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions] at whole
  cases whole with
  | tuple related => exact related

theorem Typing.CapturesType.permute {program : Program} (valid : ProgramWellFormed program) {context : Typing.Context}
    {captures : List Kernel.Capture} {types : List Term} (typed : Typing.CapturesType program context captures types)
    (permutation : RegionPermutation) :
    Typing.CapturesType program (permutation.typingContext context) (captures.map (Kernel.Capture.mapTerms permutation.term))
      (types.map permutation.term) := by
  refine ⟨?_,by simpa only [List.map_map,Function.comp_def,Kernel.Capture.mapTerms] using typed.2⟩
  have related := typed.1
  clear typed
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
    obtain ⟨shape,source,writable,located,permission⟩ := first
    refine .cons ⟨congrArg permutation.term shape,permutation.term source,writable,located.permute valid permutation,?_⟩ ih
    rcases permission with ⟨owned,equal⟩ | ⟨region,reference,notOwn,mutable⟩
    · exact Or.inl ⟨owned,equal.permute valid permutation⟩
    · refine Or.inr ⟨permutation.term region,?_,notOwn,mutable⟩
      rw [reference]
      simp only [Kernel.Capture.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions]
      congr 1

theorem Execution.ConstructorHead.permute {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {variant : Option DeclId} {fields : List Term} {head : ValueHead}
    (constructed : Execution.ConstructorHead program type variant fields head) (permutation : RegionPermutation) :
    Execution.ConstructorHead program (permutation.term type) variant (fields.map permutation.term) head := by
  rcases constructed with ⟨rfl,rfl,rfl⟩ | ⟨element,sign,width,length,rfl,rfl,rfl,count,homogeneous⟩ |
    ⟨id,arguments,data,constructor,substitution,rfl,rfl,rfl,selected,instantiated,substituted⟩
  · exact Or.inl ⟨by simp only [RegionPermutation.term,Term.renameRuntimeRegions],rfl,rfl⟩
  · refine Or.inr (Or.inl ⟨permutation.term element,sign,width,length,by simp only [RegionPermutation.term,Term.renameRuntimeRegions],rfl,rfl,
      by simpa only [List.length_map] using count,?_⟩)
    intro field member
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    exact congrArg permutation.term (homogeneous original inOriginal)
  · refine Or.inr (Or.inr ⟨id,arguments.map permutation.term,data,constructor,permutation.substitution substitution,
      by simp only [RegionPermutation.term,Term.renameRuntimeRegions],rfl,rfl,selected,instantiated.permute permutation,?_⟩)
    apply permutation.substitutes_lexical_list _ substituted
    intro term member
    obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
    exact valid.field_lexical selected.1 selected.2.1 inFields

theorem ScalarPrimitiveSignature.permute {target : TargetProfile} {primitive : Primitive} {arguments parameters : List Term} {result : Term}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters result) (permutation : RegionPermutation) :
    ScalarPrimitiveSignature target primitive (arguments.map permutation.term) (parameters.map permutation.term) (permutation.term result) := by
  cases signature <;> simp only [List.map_nil,List.map_cons,List.map_replicate,RegionPermutation.term,Term.renameRuntimeRegions]
  case integer valid => exact .integer valid
  case floating => exact .floating
  case equal valid => exact .equal valid
  case less valid => exact .less valid
  case convert source destination domain => exact .convert source destination domain

theorem RuntimeBinding.ScalarSignature.permute {binding : RuntimeBinding} {target : TargetProfile}
    {arguments : List Term} {signature : Signature} (typed : binding.ScalarSignature target arguments signature)
    (permutation : RegionPermutation) :
    binding.ScalarSignature target (arguments.map permutation.term) (permutation.signature signature) := by
  intro primitive found scalar
  exact (typed primitive found scalar).permute permutation

theorem ProgramWellFormed.binding_signature_lexical {program : Program} (valid : ProgramWellFormed program)
    {binding : RuntimeBinding} (member : binding ∈ program.input.manifest.bindings) :
    ∀ term ∈ binding.signature.terms, term.Lexical := by
  obtain ⟨_,_,_,_,_,manifest⟩ := valid.1.1
  exact manifest.2.2.2.2 binding member

theorem Typing.AtomType.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (_inventory : Kernel.BodyInventory program) {context : Typing.Context} {atom : Kernel.Atom} {type : Term}
    (typed : Typing.AtomType program context atom type) (permutation : RegionPermutation) :
    Typing.AtomType program (permutation.typingContext context) (atom.mapTerms permutation.term) (permutation.term type) := by
  cases typed <;> simp only [Kernel.Atom.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions,List.map_append]
  case constant typed => exact .constant (typed.permute valid permutation)
  case acquire located => exact .acquire (located.permute valid permutation)
  case borrow located addressable kinded writable =>
    exact .borrow (located.permute valid permutation) (addressable.permute valid permutation) (kinded.permute valid permutation) writable
  case construct fields head kinded =>
    exact .construct (fields.permute valid permutation) (head.permute valid permutation) (kinded.permute valid permutation)
  case closure found selected fields captures =>
    exact .closure found (selected.permute valid permutation) (fields.permute valid permutation)
      (captures.permute valid permutation)
  case function selected => exact .function (selected.permute valid permutation)
  case operation found selected =>
    exact .operation found (by simpa only [List.map_append,RegionPermutation.term,RegionPermutation.typingContext] using selected.permute valid permutation)
  case label member =>
    exact .label (List.mem_map.mpr ⟨_,member,rfl⟩)
  case primitive member identity instantiated kinded signature scalar operands safety effects =>
    refine .primitive member identity (instantiated.permute permutation) ?_ ?_ (scalar.permute permutation)
      (operands.permute valid permutation) safety (effects.permute valid permutation)
    · intro argument member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [permutation.term_kind,RegionPermutation.typingContext] using (kinded original present).permute permutation
    · rw [signature,permutation.signature_instantiate,permutation.lexical_signature (valid.binding_signature_lexical member)]
  case available located =>
    apply Typing.AtomType.available
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation
  case bindings located =>
    apply Typing.AtomType.bindings
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation

end Glorious.Language
