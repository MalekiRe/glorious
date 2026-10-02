import Std

namespace OwnershipMir

inductive LinearKind where
  | affine | exact
  deriving DecidableEq

inductive Kind where
  | data | affine | exact
  deriving DecidableEq

def LinearKind.kind : LinearKind → Kind
  | .affine => .affine
  | .exact => .exact

abbrev Signature := Nat → LinearKind

/-- Resolved nominal-shell metadata. Deconstruction authority is independent
of zero-use permission. A restriction never grants capabilities to children. -/
structure Shell where
  name : Nat
  restriction : Kind
  canOpen : Bool
  deriving DecidableEq

inductive Layout where
  | atom (kind : Kind)
  | nil
  | pair (left right : Layout)
  | wrap (shell : Shell) (body : Layout)
  deriving DecidableEq

/-- Ordered products encode arbitrary finite field lists; nil is the empty
payload. A hole retains its declared layout, not a fabricated resident. -/
inductive Tree (α : Type) where
  | hole (layout : Layout)
  | nil
  | leaf (value : α)
  | pair (left right : Tree α)
  | wrap (shell : Shell) (body : Tree α)
  deriving DecidableEq

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .hole t => .hole t
  | .nil => .nil
  | .leaf a => .leaf (f a)
  | .pair l r => .pair (l.map f) (r.map f)
  | .wrap s b => .wrap s (b.map f)

def Tree.layout {α : Type} (kind : α → Kind) : Tree α → Layout
  | .hole t => t
  | .nil => .nil
  | .leaf a => .atom (kind a)
  | .pair l r => .pair (l.layout kind) (r.layout kind)
  | .wrap s b => .wrap s (b.layout kind)

@[simp] theorem Tree.layout_map {α β : Type} (f : α → β) (kind : β → Kind) (tree : Tree α) :
    (tree.map f).layout kind = tree.layout (fun a => kind (f a)) := by
  induction tree <;> simp_all [Tree.map, Tree.layout]

/-- A single fold interprets both resource identity and shell obligations. -/
def Tree.mass {α : Type} (leaf : α → Nat) (shell : Shell → Nat) : Tree α → Nat
  | .hole _ | .nil => 0
  | .leaf a => leaf a
  | .pair l r => l.mass leaf shell + r.mass leaf shell
  | .wrap s b => shell s + b.mass leaf shell

abbrev Shape := Tree Kind

def Tree.ready {α : Type} : Tree α → Prop
  | .hole _ => False
  | .nil | .leaf _ => True
  | .pair l r => l.ready ∧ r.ready
  | .wrap _ b => b.ready

def Tree.copyable : Shape → Prop
  | .hole _ => False
  | .nil => True
  | .leaf k => k = .data
  | .pair l r => l.copyable ∧ r.copyable
  | .wrap s b => s.restriction = .data ∧ b.copyable

def Tree.disposable : Shape → Prop
  | .hole _ | .nil => True
  | .leaf k => k ≠ .exact
  | .pair l r => l.disposable ∧ r.disposable
  | .wrap s b => s.restriction ≠ .exact ∧ b.disposable

theorem Tree.copyable_ready {s : Shape} (copy : s.copyable) : s.ready := by
  induction s <;> simp_all [Tree.copyable, Tree.ready]

theorem Tree.copyable_disposable {s : Shape} (copy : s.copyable) : s.disposable := by
  induction s <;> simp_all [Tree.copyable, Tree.disposable]

inductive Atom where
  | data (payload : Nat)
  | owner (identity : Nat)
  deriving DecidableEq

def Atom.kind (signature : Signature) : Atom → Kind
  | .data _ => .data
  | .owner i => (signature i).kind

abbrev Value := Tree Atom

def Value.kind (signature : Signature) (value : Value) : Shape := value.map (Atom.kind signature)

def Atom.weight (identity : Nat) : Atom → Nat
  | .data _ => 0
  | .owner other => if identity = other then 1 else 0

def resourceMass (identity : Nat) (value : Value) : Nat := value.mass (Atom.weight identity) (fun _ => 0)

def shellMass (value : Value) : Nat := value.mass (fun _ => 0) (fun s => if s.restriction = .exact then 1 else 0)

theorem Value.copyable_zero {signature : Signature} {value : Value}
    (copy : (value.kind signature).copyable) (identity : Nat) : resourceMass identity value = 0 := by
  induction value with
  | hole t => simp [resourceMass, Tree.mass]
  | nil => rfl
  | leaf a =>
    cases a with
    | data _ => rfl
    | owner i => cases h : signature i <;> simp [Value.kind, Tree.map, Tree.copyable, Atom.kind, h, LinearKind.kind] at copy
  | pair l r left right =>
    simp only [Value.kind, Tree.map, Tree.copyable] at copy
    change resourceMass identity l + resourceMass identity r = 0
    rw [left copy.1, right copy.2]
  | wrap s b ih =>
    simp only [Value.kind, Tree.map, Tree.copyable] at copy
    simpa [resourceMass, Tree.mass] using ih copy.2

theorem Value.disposable_exact_zero {signature : Signature} {value : Value}
    (drop : (value.kind signature).disposable) {identity : Nat} (exactKind : signature identity = .exact) :
    resourceMass identity value = 0 := by
  induction value with
  | hole t => rfl
  | nil => rfl
  | leaf a =>
    cases a with
    | data _ => rfl
    | owner other =>
      by_cases same : identity = other
      · subst other
        simp [Value.kind, Tree.map, Tree.disposable, Atom.kind, exactKind, LinearKind.kind] at drop
      · simp [resourceMass, Tree.mass, Atom.weight, same]
  | pair l r left right =>
    simp only [Value.kind, Tree.map, Tree.disposable] at drop
    change resourceMass identity l + resourceMass identity r = 0
    rw [left drop.1, right drop.2]
  | wrap s b ih =>
    simp only [Value.kind, Tree.map, Tree.disposable] at drop
    simpa [resourceMass, Tree.mass] using ih drop.2

theorem Value.disposable_shell_zero {signature : Signature} {value : Value}
    (drop : (value.kind signature).disposable) : shellMass value = 0 := by
  induction value <;> simp_all [Value.kind, Tree.map, Tree.disposable, shellMass, Tree.mass]

/-- Even an empty or wholly moved-out payload cannot erase an exact shell. -/
theorem exact_shell_not_disposable (shell : Shell) (body : Shape)
    (exactKind : shell.restriction = .exact) : ¬ (Tree.wrap shell body).disposable := by
  simp [Tree.disposable, exactKind]

@[simp] theorem Tree.ready_map {α β : Type} (f : α → β) (tree : Tree α) :
    (tree.map f).ready ↔ tree.ready := by
  induction tree <;> simp_all [Tree.map, Tree.ready]

end OwnershipMir
