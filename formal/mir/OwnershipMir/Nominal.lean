import OwnershipMir.Focus

namespace OwnershipMir

/-- Resolved package identity and logical module path; files confer no authority. -/
structure Module where
  package : Nat
  path : List Nat
  deriving DecidableEq

def Module.Within (child parent : Module) : Prop :=
  child.package = parent.package ∧ parent.path.IsPrefix child.path

inductive Visibility where
  | hidden | exported | package | parent
  deriving DecidableEq

def Visibility.Allows (visibility : Visibility) (owner caller : Module) : Prop :=
  match visibility with
  | .hidden => caller.Within owner
  | .exported => True
  | .package => caller.package = owner.package
  | .parent => caller.Within {owner with path := owner.path.dropLast}

/-- Ordered declared fields. Groups encode field order, not additional fields;
a field may itself have an arbitrary structural or nominal layout. -/
inductive Fields where
  | empty
  | field (visibility : Visibility) (layout : Layout)
  | group (left right : Fields)
  deriving DecidableEq

def Fields.layout : Fields → Layout
  | .empty => .nil
  | .field _ layout => layout
  | .group left right => .pair left.layout right.layout

def Fields.Visible (owner caller : Module) : Fields → Prop
  | .empty => True
  | .field visibility _ => visibility.Allows owner caller
  | .group left right => left.Visible owner caller ∧ right.Visible owner caller

/-- Finite instantiated structural declarations. Custom destruction and
indirect/recursive type elaboration are not represented by this ownership IR. -/
structure Declaration where
  owner : Module
  restriction : Kind
  fields : Fields
  deriving DecidableEq

abbrev Declarations := Nat → Option Declaration

structure Authority where
  declarations : Declarations
  module : Module

/-- Cached layout metadata must agree with its resolved declaration. Holes
retain layouts and therefore remain subject to the same validation. -/
inductive Layout.Declared (declarations : Declarations) : Layout → Prop where
  | atom (kind) : Declared declarations (.atom kind)
  | nil : Declared declarations .nil
  | pair {left right} (l : Declared declarations left) (r : Declared declarations right) :
      Declared declarations (.pair left right)
  | wrap {shell body declaration} (resolved : declarations shell.name = some declaration)
      (restriction : shell.restriction = declaration.restriction)
      (payload : body = declaration.fields.layout) (nested : Declared declarations body) :
      Declared declarations (.wrap shell body)

def Authority.CanOpen (authority : Authority) (shell : Shell) (body : Layout) : Prop :=
  ∃ declaration, authority.declarations shell.name = some declaration ∧
    shell.restriction = declaration.restriction ∧ body = declaration.fields.layout ∧
    declaration.fields.Visible declaration.owner authority.module

mutual
  /-- Whole-owner transfer needs no representation visibility. Crossing a
  nominal body checks the selected declared fields, never a guessed layout. -/
  inductive Layout.Accessible (authority : Authority) : Layout → List Direction → Layout → Prop where
    | whole (layout) : Layout.Accessible authority layout [] layout
    | left {left right path selected} (inside : Layout.Accessible authority left path selected) :
        Layout.Accessible authority (.pair left right) (.left :: path) selected
    | right {left right path selected} (inside : Layout.Accessible authority right path selected) :
        Layout.Accessible authority (.pair left right) (.right :: path) selected
    | body {shell body declaration path selected}
        (resolved : authority.declarations shell.name = some declaration)
        (restriction : shell.restriction = declaration.restriction)
        (payload : body = declaration.fields.layout)
        (inside : Fields.Accessible authority declaration.owner declaration.fields path selected) :
        Layout.Accessible authority (.wrap shell body) (.body :: path) selected

  inductive Fields.Accessible (authority : Authority) :
      Module → Fields → List Direction → Layout → Prop where
    | whole {owner fields} (visible : fields.Visible owner authority.module) :
        Fields.Accessible authority owner fields [] fields.layout
    | field {owner visibility layout path selected} (visible : visibility.Allows owner authority.module)
        (inside : Layout.Accessible authority layout path selected) :
        Fields.Accessible authority owner (.field visibility layout) path selected
    | left {owner left right path selected} (inside : Fields.Accessible authority owner left path selected) :
        Fields.Accessible authority owner (.group left right) (.left :: path) selected
    | right {owner left right path selected} (inside : Fields.Accessible authority owner right path selected) :
        Fields.Accessible authority owner (.group left right) (.right :: path) selected
end

theorem Authority.open_declared {authority : Authority} {shell : Shell} {body : Layout}
    (allowed : authority.CanOpen shell body) :
    ∃ declaration, authority.declarations shell.name = some declaration ∧
      shell.restriction = declaration.restriction ∧ body = declaration.fields.layout ∧
      declaration.fields.Visible declaration.owner authority.module := allowed

theorem Authority.private_field_denied {authority : Authority} {shell : Shell} {layout : Layout}
    {declaration : Declaration} (resolved : authority.declarations shell.name = some declaration)
    (fields : declaration.fields = .field .hidden layout)
    (outside : ¬ authority.module.Within declaration.owner) :
    ¬ authority.CanOpen shell layout := by
  rintro ⟨actual, selected, _, _, visible⟩
  cases Option.some.inj (resolved.symm.trans selected)
  exact outside (by simpa [fields, Fields.Visible, Visibility.Allows] using visible)

theorem Layout.Accessible.private_field_denied {authority : Authority} {shell : Shell} {body layout selected : Layout}
    {declaration : Declaration} {path : List Direction}
    (resolved : authority.declarations shell.name = some declaration)
    (fields : declaration.fields = .field .hidden layout)
    (outside : ¬ authority.module.Within declaration.owner) :
    ¬ Layout.Accessible authority (.wrap shell body) (.body :: path) selected := by
  intro access
  cases access with
  | body found restriction payload inside =>
    cases Option.some.inj (resolved.symm.trans found)
    rw [fields] at inside
    cases inside with
    | whole visible => exact outside visible
    | field visible nested => exact outside visible


end OwnershipMir
