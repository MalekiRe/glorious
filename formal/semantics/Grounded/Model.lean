import Grounded.Identifiers
/-! Decoded language vocabulary and declarations. Program records contain no checking
or execution certificates. Lexical uses carry resolved binding identities. -/
namespace Grounded

/-- The selected target supplies its positive pointer width (§4.4). Other ABI
properties enter when their semantic consumers are introduced. -/
structure Target where
  pointerBits : Nat
  positive : 0 < pointerBits

inductive Width where
  | w8 | w16 | w32 | w64 | w128
  | pointer
  deriving DecidableEq

def Width.bits (target : Target) : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128
  | .pointer => target.pointerBits

structure IntegerType where
  signed : Bool
  width : Width
  deriving DecidableEq

/-- Mathematical scalar range; there is no implicit wrapping of literals. -/
def IntegerType.Contains (target : Target) (type : IntegerType) (value : Int) : Prop :=
  let bound : Int := 2 ^ (type.width.bits target - if type.signed then 1 else 0)
  (if type.signed then -bound else 0) ≤ value ∧ value < bound

def UnicodeScalar (number : Nat) : Prop :=
  number < 0x110000 ∧ (number < 0xd800 ∨ 0xe000 ≤ number)

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character
  | tuple (head : Ty) (tail : List Ty)
  | array (element : Ty) (length : Nat)
  | nominal (identity : Nat)
/-- Decoded type expressions retain alias references until static resolution. -/
inductive TypeExpr where
  | concrete (type : Ty)
  | alias (name : String)
  | tuple (head : TypeExpr) (tail : List TypeExpr)
  | array (element : TypeExpr) (length : Nat)

abbrev Aliases := String → Option TypeExpr
/-- Resolved module identity, including the package boundary (§2.2). -/
structure Module where
  package : Nat
  path : List Identifier
  deriving DecidableEq

inductive Visibility where
  | «private» | package | parent | «public»

def Visibility.Allows (visibility : Visibility) (owner caller : Module) : Prop :=
  match visibility with
  | .private => caller.package = owner.package ∧ owner.path.IsPrefix caller.path
  | .package => caller.package = owner.package
  | .parent => owner.path ≠ [] ∧ caller.package = owner.package ∧
      owner.path.dropLast.IsPrefix caller.path
  | .public => True

/-- A declared visibility must designate a scope containing its owner.
In particular, a package root has no parent scope. -/
def Visibility.ValidAt (visibility : Visibility) (owner : Module) : Prop :=
  visibility.Allows owner owner

theorem Visibility.validAt_iff (visibility : Visibility) (owner : Module) :
    visibility.ValidAt owner ↔ (visibility = .parent → owner.path ≠ []) := by
  cases visibility <;> simp [Visibility.ValidAt, Visibility.Allows, List.dropLast_prefix]

theorem Visibility.ValidAt.not_parent_at_root {visibility : Visibility} {owner : Module}
    (valid : visibility.ValidAt owner) (root : owner.path = []) : visibility ≠ .parent := by
  intro same
  subst visibility
  exact valid.1 root


theorem Visibility.Allows.descendant {visibility : Visibility} {owner caller child : Module}
    (allowed : visibility.Allows owner caller) (same : child.package = caller.package)
    (enclosing : caller.path.IsPrefix child.path) : visibility.Allows owner child := by
  cases visibility with
  | «private» => exact ⟨same.trans allowed.1, allowed.2.trans enclosing⟩
  | package => exact same.trans allowed
  | parent => exact ⟨allowed.1, same.trans allowed.2.1, allowed.2.2.trans enclosing⟩
  | «public» => trivial


inductive FieldKey where
  | named (name : String)
  | positional (index : Nat)

/-- A resolved lexical declaration identity, not a source spelling or a runtime
storage address. Recursive invocations reuse it in distinct environments. -/
structure BindingId where
  index : Nat
  deriving DecidableEq


structure Place where
  root : BindingId
  fields : List FieldKey := []

structure Field where
  type : Ty
  visibility : Visibility := .private

/-- Declaration order is retained even for named fields. -/
inductive Fields where
  | tuple (fields : List Field)
  | record (fields : List (String × Field))

def Fields.residents : Fields → List Field
  | .tuple fields => fields
  | .record fields => fields.map Prod.snd

def Fields.Valid : Fields → Prop
  | .tuple _ => True
  | .record fields => (fields.map Prod.fst).Nodup

def Fields.index : Fields → FieldKey → Option Nat
  | .tuple fields, .positional index => if index < fields.length then some index else none
  | .record fields, .named name => fields.findIdx? (fun field => field.1 == name)
  | _, _ => none

inductive DataShape where
  | «structure» (fields : Fields)
  | enumeration (variants : List Fields)

inductive Principal where
  | duplicable | affine | exact

structure DataDecl where
  home : Module
  visibility : Visibility := .private
  shape : DataShape
  restriction : Option Principal := none

def DataDecl.schemas (declaration : DataDecl) : List Fields :=
  match declaration.shape with
  | .structure fields => [fields]
  | .enumeration variants => variants

/-- No variant tag denotes a struct; an explicit tag denotes an enum variant. -/
def DataDecl.constructor (declaration : DataDecl) (tag : Option Nat) : Option Fields :=
  match declaration.shape, tag with
  | .structure fields, none => some fields
  | .enumeration variants, some index => variants[index]?
  | _, _ => none

abbrev DataDeclarations := Nat → Option DataDecl
/-- Constructor identity for structural matching; tuples remain distinct from nominal data. -/
inductive Head where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple | array
  | nominal (identity : Nat) (tag : Option Nat)
  deriving DecidableEq

inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)
  | array (elements : List Value)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List Value)

inductive Pattern where
  | wildcard
  | binder (name : BindingId) (type : Ty)
  | node (head : Head) (fields : List Pattern)
  /-- Some records the constant type; None is the untyped coverage form. -/
  | literal (type : Option Ty) (value : Value)


structure BindingType where
  type : Ty
  mutable : Bool := false

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | read (place : Place)
  | move (place : Place)
  | sequence (first rest : Expr)
  | bind (mutable : Bool) (name : BindingId) (localType : Ty) (initial body : Expr)
  | tuple (head : Expr) (tail : List Expr)
  | project (body : Expr) (key : FieldKey)
  | array (elements : List Expr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List Expr)
  | call (identity : Nat) (arguments : List Expr)
  | assign (place : Place) (value rest : Expr)
  | applyPatterns (inputs : List Ty) (arguments : List Expr) (arms : List (Pattern × Expr))

structure ConstantDecl where
  home : Module
  visibility : Visibility := .private
  type : TypeExpr
  body : Expr

abbrev Constants := String → Option ConstantDecl

/-- Direct, noncapturing, effect-free functions; omitted results denote unit. -/
structure FunctionDecl where
  home : Module
  visibility : Visibility := .private
  parameters : List (BindingId × BindingType)
  result : Ty := .unit
  body : Expr

/-- One immutable decoded program supplies the facts shared by static and
dynamic semantics. It carries source declarations, never execution guarantees. -/
structure Program where
  target : Target
  aliases : Aliases
  constants : Constants
  data : DataDeclarations
  functions : Nat → Option FunctionDecl

/-- Resolve an already-selected lexical identity; independent of its payload. -/
def lookup {α : Type} (name : BindingId) : List (BindingId × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

theorem lookup.map {α β : Type} (name : BindingId) (transform : α → β)
    (entries : List (BindingId × α)) :
    lookup name (entries.map fun entry => (entry.1, transform entry.2)) =
      (lookup name entries).map transform := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp only [List.map_cons, lookup]
    split <;> simp_all

theorem lookup.mem {α : Type} {name : BindingId} {value : α} {entries : List (BindingId × α)}
    (found : lookup name entries = some value) : (name, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    cases entry with
    | mk key old =>
      simp only [lookup] at found
      split at found
      next same => subst key; cases found; exact List.mem_cons_self
      next different => exact List.mem_cons_of_mem _ (ih found)

theorem lookup.unique_key {α : Type} {firstName secondName : BindingId} {value : α}
    {entries : List (BindingId × α)} (distinct : (entries.map Prod.snd).Nodup)
    (first : lookup firstName entries = some value) (second : lookup secondName entries = some value) :
    firstName = secondName := by
  induction entries with
  | nil => simp [lookup] at first
  | cons entry rest ih =>
    cases entry with
    | mk key resident =>
      have parts := List.nodup_cons.mp distinct
      simp only [lookup] at first second
      split at first
      next same =>
        subst firstName
        have equal := Option.some.inj first
        subst resident
        split at second
        next same => exact same.symm
        next different =>
          exact False.elim (parts.1 (List.mem_map.mpr ⟨(secondName, value), lookup.mem second, rfl⟩))
      next different =>
        split at second
        next same =>
          have equal := Option.some.inj second
          subst resident
          exact False.elim (parts.1 (List.mem_map.mpr ⟨(firstName, value), lookup.mem first, rfl⟩))
        next missed => exact ih parts.2 first second


/-- Replace the selected lexical payload without changing binding identities. -/
def replaceBinding {α : Type} (name : BindingId) (value : α) : List (BindingId × α) → Option (List (BindingId × α))
  | [] => none
  | (key, old) :: rest =>
      if key = name then some ((key, value) :: rest)
      else ((key, old) :: ·) <$> replaceBinding name value rest

theorem replaceBinding.map_same {α β : Type} {name : BindingId} {old value : α}
    {before after : List (BindingId × α)} (transform : α → β)
    (selected : lookup name before = some old)
    (written : replaceBinding name value before = some after) (same : transform value = transform old) :
    (after.map fun entry => (entry.1, transform entry.2)) =
      (before.map fun entry => (entry.1, transform entry.2)) := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    cases entry with
    | mk key resident =>
      simp only [replaceBinding] at written
      split at written
      next equal =>
        subst key
        simp [lookup] at selected
        subst resident
        cases written
        simp only [List.map_cons, same]
      next different =>
        simp only [lookup, if_neg (Ne.symm different)] at selected
        obtain ⟨tail, replaced, equal⟩ := Option.map_eq_some_iff.mp written
        subst after
        exact congrArg (List.cons (key, transform resident)) (ih selected replaced)

theorem replaceBinding.all {α : Type} {name : BindingId} {value : α}
    {before after : List (BindingId × α)} {predicate : α → Prop}
    (written : replaceBinding name value before = some after)
    (current : ∀ entry ∈ before, predicate entry.2) (replacement : predicate value) :
    ∀ entry ∈ after, predicate entry.2 := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    cases entry with
    | mk key resident =>
      have head := current (key, resident) (List.mem_cons_self)
      have tail : ∀ entry ∈ rest, predicate entry.2 := fun entry member => current entry (List.mem_cons_of_mem _ member)
      simp only [replaceBinding] at written
      split at written
      next equal =>
        cases written
        intro entry member
        rcases List.mem_cons.mp member with same | member
        · subst entry; exact replacement
        · exact tail entry member
      next different =>
        obtain ⟨remaining, replaced, equal⟩ := Option.map_eq_some_iff.mp written
        subst after
        intro entry member
        rcases List.mem_cons.mp member with same | member
        · subst entry; exact head
        · exact ih replaced tail entry member


theorem lookup.of_mem {α : Type} {name : BindingId} {value : α} {entries : List (BindingId × α)}
    (distinct : (entries.map Prod.fst).Nodup) (member : (name, value) ∈ entries) :
    lookup name entries = some value := by
  induction entries with
  | nil => cases member
  | cons entry rest ih =>
    rcases entry with ⟨key, resident⟩
    rcases List.mem_cons.mp member with same | tailMember
    · cases same; simp [lookup]
    · have parts := List.nodup_cons.mp distinct
      have different : name ≠ key := by
        intro same
        subst key
        exact parts.1 (List.mem_map.mpr ⟨(name, value), tailMember, rfl⟩)
      simpa [lookup, different] using ih parts.2 tailMember


theorem replaceBinding.lookup_after {α : Type} {name : BindingId} {value : α}
    {before after : List (BindingId × α)} (written : replaceBinding name value before = some after) :
    lookup name after = some value := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    simp only [replaceBinding] at written
    split at written
    next same => cases written; simp [lookup, same]
    next different =>
      obtain ⟨tail, replaced, same⟩ := Option.map_eq_some_iff.mp written
      subst after
      simp [lookup, Ne.symm different, ih replaced]

theorem replaceBinding.overwrite {α : Type} {name : BindingId} {first second : α}
    {before middle after : List (BindingId × α)}
    (written : replaceBinding name first before = some middle)
    (rewritten : replaceBinding name second middle = some after) :
    replaceBinding name second before = some after := by
  induction before generalizing middle after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    simp only [replaceBinding] at written
    split at written
    next same =>
      cases written
      simpa only [replaceBinding, if_pos same] using rewritten
    next different =>
      obtain ⟨tail, replaced, same⟩ := Option.map_eq_some_iff.mp written
      subst middle
      simp only [replaceBinding, if_neg different] at rewritten
      obtain ⟨final, replacedAgain, same⟩ := Option.map_eq_some_iff.mp rewritten
      subst after
      simp [replaceBinding, different, ih replaced replacedAgain]


end Grounded
