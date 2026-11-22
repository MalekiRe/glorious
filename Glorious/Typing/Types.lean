module

public import Glorious.Core.Semantics

/-!
# Types for Core, and the regions in them

A reference's type names the region it points into. In the typing of a
function a region is a variable; at run time it is a memory cell. A callable's
type can bind regions, so that it can be called with references into cells
that did not exist when it was made, and lists the regions a call may touch.

Everything done to the regions of a type is one of two traversals, `mapR` and
`regionsAt`, so that the facts about instantiating region variables and
opening a callable's bound regions are each proved once about those.
-/

@[expose] public section

namespace Glorious.Typing

/-- Where a reference points. -/
inductive Rgn where
  /-- A region of the function being typed: one fixed when it was made, or one
  it is called with. -/
  | var (i : Nat)
  /-- A region bound by an enclosing callable type, counted outwards from the
  nearest one that binds regions. -/
  | bound (k : Nat)
  /-- At run time: the memory cell at this address. -/
  | cell (a : Nat)
  /-- At run time: the label scope with this identity. -/
  | lab (id : Nat)
  /-- At run time: the borrow with this identity. -/
  | loan (b : Nat)
  /-- Not a place but a permission: to write what `r` is. Being allowed to
  touch `r` is being allowed to read it. -/
  | wr (r : Rgn)
  /-- One place or another: a reference of this region points into one of
  them, and touching it needs both. -/
  | or (a b : Rgn)
  deriving DecidableEq

inductive Ty where
  | int
  | tuple (fields : List Ty)
  /-- A declared data type applied to its arguments. -/
  | data (name : Nat) (args : List Ty)
  /-- A callable: a function, a resumption or a label. It binds `rgns` regions,
  chosen at each call. `eff` lists the operations it may perform, each with the
  type arguments of its effect. `once` says that it may be called at most once.
  `env`, if given, says that it is a function that captured values of exactly
  these types: its environment, which another function written against the same
  environment can take over. `acc` lists the regions a call may read or write. -/
  | fn (rgns : Nat) (params : List Ty) (ret : Ty) (eff : List (Nat × List Ty)) (once : Bool)
      (env : Option (List Ty)) (acc : List Rgn)
  /-- A reference to a cell of region `ρ` holding a `t`. -/
  | ref (ρ : Rgn) (t : Ty)
  /-- The result of a call that does not return. No value has this type. -/
  | never

/-- The type of an operation: its payload, and what it is resumed with if it
can be resumed at all. -/
abbrev OpTy := List Ty × Option Ty

/-- The operations available somewhere, nearest handler first, each with the
type arguments of its effect. -/
abbrev Row := List (Nat × List Ty)

def Ty.unit : Ty := .tuple []

/-- Everything `a` offers, `b` offers at the same type: code written for `a`
can run where `b` is available. -/
def Row.le (a b : Row) : Prop :=
  ∀ op sig, a.lookup op = some sig → b.lookup op = some sig

/-! ## Regions -/

namespace Rgn

/-- Is no part of this region one bound by a callable type? -/
def free : Rgn → Bool
  | .bound _ => false
  | .var _ => true
  | .cell _ => true
  | .lab _ => true
  | .loan _ => true
  | .wr r => r.free
  | .or a b => a.free && b.free

/-- Is this region a place, or one of several places: nothing bound by a
callable type and no permission? -/
def place : Rgn → Bool
  | .bound _ => false
  | .wr _ => false
  | .or a b => a.place && b.place
  | _ => true

/-- A region to put in place of another: never one that would be bound where
it lands, and a place, not a permission. -/
def clean : Option Rgn → Rgn
  | some r => if r.place then r else .cell 0
  | none => .cell 0

/-- Put regions in place of a function's region variables. -/
def inst (θ : List Rgn) : Rgn → Rgn
  | .var i => clean θ[i]?
  | .wr r => .wr (inst θ r)
  | .or a b => .or (inst θ a) (inst θ b)
  | r => r

/-- Put regions in place of those bound by the outermost callable type, seen
from under `d` regions bound further in. -/
def openAt (d : Nat) (rs : List Rgn) : Rgn → Rgn
  | .bound j =>
    if j < d then .bound j
    else
      match rs[j - d]? with
      | some r => clean (some r)
      | none => .bound (j - rs.length)
  | .wr r => .wr (openAt d rs r)
  | .or a b => .or (openAt d rs a) (openAt d rs b)
  | r => r

theorem place_free {r : Rgn} (h : r.place = true) : r.free = true := by
  induction r with
  | var i => rfl
  | bound k => cases h
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r _ => cases h
  | or a b iha ihb =>
    simp only [place, Bool.and_eq_true] at h
    simp [free, iha h.1, ihb h.2]

theorem clean_place (o : Option Rgn) : (clean o).place = true := by
  cases o with
  | none => rfl
  | some r =>
    by_cases h : r.place = true
    · simp [clean, h]
    · simp [clean, h, place]

theorem clean_free (o : Option Rgn) : (clean o).free = true := place_free (clean_place o)

theorem inst_free (θ : List Rgn) (r : Rgn) : (r.inst θ).free = r.free := by
  induction r with
  | var i => exact clean_free _
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact ih
  | or a b iha ihb => simp [inst, free, iha, ihb]

theorem inst_place (θ : List Rgn) (r : Rgn) : (r.inst θ).place = r.place := by
  induction r with
  | var i => exact clean_place _
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r _ => rfl
  | or a b iha ihb => simp [inst, place, iha, ihb]

theorem inst_clean (θ : List Rgn) (o : Option Rgn) : (clean o).inst θ = clean (o.map (inst θ)) := by
  cases o with
  | none => rfl
  | some r =>
    by_cases h : r.place = true
    · have h' : (r.inst θ).place = true := by rw [inst_place]; exact h
      simp [clean, h, h']
    · have h' : ¬ (r.inst θ).place = true := by rw [inst_place]; exact h
      simp [clean, h, h', inst]

/-- Opening leaves a region that is not bound alone. -/
theorem openAt_free {r : Rgn} (h : r.free = true) (d : Nat) (rs : List Rgn) :
    r.openAt d rs = r := by
  induction r with
  | var i => rfl
  | bound k => cases h
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr (ih h)
  | or a b iha ihb =>
    simp only [free, Bool.and_eq_true] at h
    simp [openAt, iha h.1, ihb h.2]

/-- Instantiating twice is instantiating once, by the regions instantiated. -/
theorem inst_inst (θ η : List Rgn) (r : Rgn) :
    (r.inst θ).inst η = r.inst (θ.map (inst η)) := by
  induction r with
  | var i =>
    show (clean θ[i]?).inst η = clean ((θ.map (inst η))[i]?)
    rw [List.getElem?_map, inst_clean]
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih
  | or a b iha ihb => simp [inst, iha, ihb]

/-- Opening and then instantiating is instantiating and then opening. -/
theorem openAt_inst (d : Nat) (rs η : List Rgn) (r : Rgn) :
    (r.openAt d rs).inst η = (r.inst η).openAt d (rs.map (inst η)) := by
  induction r with
  | var i => exact (openAt_free (clean_free _) d _).symm
  | bound j =>
    by_cases hj : j < d
    · simp [openAt, hj, inst]
    · cases h : rs[j - d]? with
      | none => simp [openAt, hj, h, inst]
      | some x =>
        have hm : (rs.map (inst η))[j - d]? = some (x.inst η) := by simp [h]
        have hl : (Rgn.bound j).openAt d rs = clean (some x) := by simp [openAt, hj, h]
        have hr : (Rgn.bound j).openAt d (rs.map (inst η)) = clean (some (x.inst η)) := by
          simp [openAt, hj, hm]
        show ((Rgn.bound j).openAt d rs).inst η = (Rgn.bound j).openAt d (rs.map (inst η))
        rw [hl, hr, inst_clean]
        rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih
  | or a b iha ihb => simp [openAt, inst, iha, ihb]

/-- Opening with no regions changes nothing. -/
theorem openAt_nil (d : Nat) (r : Rgn) : r.openAt d [] = r := by
  induction r with
  | var i => rfl
  | bound j =>
    by_cases hj : j < d <;> simp [openAt, hj]
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih
  | or a b iha ihb => simp [openAt, iha, ihb]

/-- The variables a function's call regions are opened to in its body: those
after its `c` capture regions. -/
def callVars (c n : Nat) : List Rgn := (List.range n).map fun j => .var (c + j)

theorem callVars_length (c n : Nat) : (callVars c n).length = n := by simp [callVars]

/-- A region variable below `c`, or not a variable at all. -/
def within (c : Nat) : Rgn → Bool
  | .var i => decide (i < c)
  | .bound _ => true
  | .cell _ => true
  | .lab _ => true
  | .loan _ => true
  | .wr r => within c r
  | .or a b => within c a && within c b

/-- A function's body is typed with its call regions as variables. Entered
with capture regions `θ` and call regions `rs`, a region of its signature means
what the signature's type, instantiated and opened, says. -/
theorem open_callVars_inst (d : Nat) (θ rs : List Rgn) (r : Rgn) (hr : r.within θ.length = true) :
    (r.openAt d (callVars θ.length rs.length)).inst (θ ++ rs) = (r.inst θ).openAt d rs := by
  induction r with
  | var i =>
    have hi : i < θ.length := by simpa [within] using hr
    show clean (θ ++ rs)[i]? = (clean θ[i]?).openAt d rs
    rw [List.getElem?_append_left hi, openAt_free (clean_free _)]
  | bound j =>
    by_cases hj : j < d
    · simp [openAt, hj, inst]
    · by_cases hlt : j - d < rs.length
      · have h1 : (callVars θ.length rs.length)[j - d]? = some (.var (θ.length + (j - d))) := by
          simp [callVars, hlt]
        have h2 : (θ ++ rs)[θ.length + (j - d)]? = rs[j - d]? := by
          rw [List.getElem?_append_right (Nat.le_add_right _ _)]
          simp
        have hl : (Rgn.bound j).openAt d (callVars θ.length rs.length)
            = .var (θ.length + (j - d)) := by
          simp [openAt, hj, h1, clean, place]
        have hx : rs[j - d]? = some rs[j - d] := by simp [hlt]
        have hr' : (Rgn.bound j).openAt d rs = clean (some rs[j - d]) := by
          simp [openAt, hj, hx]
        show ((Rgn.bound j).openAt d (callVars θ.length rs.length)).inst (θ ++ rs)
          = (Rgn.bound j).openAt d rs
        rw [hl, hr']
        show clean (θ ++ rs)[θ.length + (j - d)]? = _
        rw [h2, hx]
      · have h1 : (callVars θ.length rs.length)[j - d]? = none := by
          simp [callVars]
          omega
        have h2 : rs[j - d]? = none := by
          simp
          omega
        simp [openAt, hj, h1, h2, inst, callVars_length]
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr (ih hr)
  | or a b iha ihb =>
    simp only [within, Bool.and_eq_true] at hr
    simp [openAt, inst, iha hr.1, ihb hr.2]

/-- No part of the region is bound more than `d` callable types out. -/
def lcAt (d : Nat) : Rgn → Bool
  | .bound j => decide (j < d)
  | .wr r => lcAt d r
  | .or a b => lcAt d a && lcAt d b
  | _ => true

theorem place_lcAt {r : Rgn} (h : r.place = true) (d : Nat) : r.lcAt d = true := by
  induction r with
  | bound k => cases h
  | wr r _ => cases h
  | or a b iha ihb =>
    simp only [place, Bool.and_eq_true] at h
    simp [lcAt, iha h.1, ihb h.2]
  | _ => rfl

theorem lcAt_inst {d : Nat} {r : Rgn} (h : r.lcAt d = true) (θ : List Rgn) :
    (r.inst θ).lcAt d = true := by
  induction r with
  | var i => exact place_lcAt (clean_place _) d
  | bound k => exact h
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact ih h
  | or a b iha ihb =>
    simp only [lcAt, Bool.and_eq_true] at h
    simp [inst, lcAt, iha h.1, ihb h.2]

/-- Does the region have no part that is a region variable? -/
def novar : Rgn → Bool
  | .var _ => false
  | .wr r => novar r
  | .or a b => novar a && novar b
  | _ => true

/-- Is the region none of the `n` regions a callable type binds, seen from
inside it? -/
def freeOf (n : Nat) : Rgn → Bool
  | .bound k => n ≤ k
  | .wr r => freeOf n r
  | .or a b => freeOf n a && freeOf n b
  | _ => true

theorem freeOf_of_free {n : Nat} : ∀ {r : Rgn}, r.free = true → r.freeOf n = true
  | .bound _, h => by cases h
  | .wr r, h => freeOf_of_free (r := r) h
  | .or a b, h => by
    simp only [free, Bool.and_eq_true] at h
    simp [freeOf, freeOf_of_free h.1, freeOf_of_free h.2]
  | .var _, _ | .cell _, _ | .lab _, _ | .loan _, _ => rfl

theorem freeOf_zero : ∀ r : Rgn, r.freeOf 0 = true
  | .bound _ => by simp [freeOf]
  | .wr r => freeOf_zero r
  | .or a b => by simp [freeOf, freeOf_zero a, freeOf_zero b]
  | .var _ | .cell _ | .lab _ | .loan _ => rfl

/-- The places and permissions a region is made of: a region that is one of
several places is each of them. -/
def parts : Rgn → List Rgn
  | .wr r => (parts r).map .wr
  | .or a b => parts a ++ parts b
  | r => [r]

/-- A region that is not several places: a place, or leave to write one. -/
def atom : Rgn → Bool
  | .or _ _ => false
  | .wr r => r.atom
  | _ => true

theorem atom_parts {r : Rgn} (h : r.atom = true) : r.parts = [r] := by
  induction r with
  | or a b _ _ => cases h
  | wr r ih => simp [parts, ih h]
  | _ => rfl

theorem mem_parts_atom {r x : Rgn} (h : x ∈ r.parts) : x.atom = true := by
  induction r generalizing x with
  | or a b iha ihb =>
    simp only [parts, List.mem_append] at h
    rcases h with h | h
    · exact iha h
    · exact ihb h
  | wr r ih =>
    simp only [parts, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    have := ih (x := y) hy
    simpa [atom] using this
  | _ =>
    simp only [parts, List.mem_singleton] at h
    subst h
    rfl

/-- A part of a region is its own only part. -/
theorem parts_of_mem {r x : Rgn} (h : x ∈ r.parts) : x.parts = [x] := atom_parts (mem_parts_atom h)

theorem self_mem_parts {x : Rgn} (h : x.atom = true) : x ∈ x.parts := by
  rw [atom_parts h]
  exact List.mem_singleton_self x

theorem parts_inst (θ : List Rgn) (r : Rgn) :
    (r.inst θ).parts = r.parts.flatMap fun x => (x.inst θ).parts := by
  induction r with
  | or a b iha ihb => simp [inst, parts, iha, ihb, List.flatMap_append]
  | wr r ih => simp [inst, parts, ih, List.flatMap_map, List.map_flatMap]
  | _ => simp [parts]

theorem parts_openAt (d : Nat) (rs : List Rgn) (r : Rgn) :
    (r.openAt d rs).parts = r.parts.flatMap fun x => (x.openAt d rs).parts := by
  induction r with
  | or a b iha ihb => simp [openAt, parts, iha, ihb, List.flatMap_append]
  | wr r ih => simp [openAt, parts, ih, List.flatMap_map, List.map_flatMap]
  | _ => simp [parts]

theorem free_of_mem_parts {r x : Rgn} (hx : x ∈ r.parts) (hf : r.free = true) : x.free = true := by
  induction r generalizing x with
  | or a b iha ihb =>
    simp only [free, Bool.and_eq_true] at hf
    simp only [parts, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha hx hf.1
    · exact ihb hx hf.2
  | wr r ih =>
    simp only [parts, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := ih (x := y) hy hf
    simpa [free] using this
  | _ =>
    simp only [parts, List.mem_singleton] at hx
    subst hx
    exact hf

/-- A part bound by a callable type is left as it is. -/
theorem inst_atom_bound {x : Rgn} (ha : x.atom = true) (hf : x.free = false) (θ : List Rgn) :
    x.inst θ = x := by
  induction x with
  | var i => cases hf
  | wr r ih => exact congrArg Rgn.wr (ih ha hf)
  | or a b _ _ => cases ha
  | _ => rfl

/-- A place has no part that is leave to write. -/
theorem place_parts {r x : Rgn} (h : r.place = true) (hx : x ∈ r.parts) : ∀ y, x ≠ .wr y := by
  induction r generalizing x with
  | or a b iha ihb =>
    simp only [place, Bool.and_eq_true] at h
    simp only [parts, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha h.1 hx
    · exact ihb h.2 hx
  | wr r _ => cases h
  | bound k => cases h
  | _ =>
    simp only [parts, List.mem_singleton] at hx
    subst hx
    intro y hy
    cases hy

/-- What a variable is instantiated to has no part that is leave to write. -/
theorem inst_var_parts {θ : List Rgn} {i : Nat} {x : Rgn} (hx : x ∈ ((Rgn.var i).inst θ).parts) :
    ∀ y, x ≠ .wr y := place_parts (clean_place _) hx

end Rgn

/-! ## The two traversals -/

mutual

/-- Apply `f` to every region of a type, telling it how many bound regions are
in scope where the region stands. -/
def Ty.mapR (f : Nat → Rgn → Rgn) : Nat → Ty → Ty
  | _, .int => .int
  | k, .tuple fs => .tuple (Ty.mapRs f k fs)
  | k, .data n args => .data n (Ty.mapRs f k args)
  | k, .fn n ps r e once env acc =>
    .fn n (Ty.mapRs f (k + n) ps) (Ty.mapR f (k + n) r) (Ty.mapRow f (k + n) e) once
      (Ty.mapEnv f (k + n) env) (acc.map (f (k + n)))
  | k, .ref ρ t => .ref (f k ρ) (Ty.mapR f k t)
  | _, .never => .never
termination_by structural _ t => t

def Ty.mapRs (f : Nat → Rgn → Rgn) : Nat → List Ty → List Ty
  | _, [] => []
  | k, t :: ts => Ty.mapR f k t :: Ty.mapRs f k ts
termination_by structural _ ts => ts

def Ty.mapRow (f : Nat → Rgn → Rgn) : Nat → List (Nat × List Ty) → List (Nat × List Ty)
  | _, [] => []
  | k, e :: es => Ty.mapEntry f k e :: Ty.mapRow f k es
termination_by structural _ es => es

def Ty.mapEntry (f : Nat → Rgn → Rgn) : Nat → Nat × List Ty → Nat × List Ty
  | k, (op, ts) => (op, Ty.mapRs f k ts)
termination_by structural _ e => e

def Ty.mapEnv (f : Nat → Rgn → Rgn) : Nat → Option (List Ty) → Option (List Ty)
  | _, none => none
  | k, some ts => some (Ty.mapRs f k ts)
termination_by structural _ env => env

end

mutual

/-- Every region of a type, in order, each with the number of bound regions in
scope where it stands. -/
def Ty.regionsAt : Nat → Ty → List (Nat × Rgn)
  | _, .int => []
  | k, .tuple fs => Ty.regionsAts k fs
  | k, .data _ args => Ty.regionsAts k args
  | k, .fn n ps r e _ env acc =>
    Ty.regionsAts (k + n) ps ++ (Ty.regionsAt (k + n) r ++ (Ty.regionsRow (k + n) e
      ++ (Ty.regionsEnv (k + n) env ++ acc.map fun x => (k + n, x))))
  | k, .ref ρ t => (k, ρ) :: Ty.regionsAt k t
  | _, .never => []
termination_by structural _ t => t

def Ty.regionsAts : Nat → List Ty → List (Nat × Rgn)
  | _, [] => []
  | k, t :: ts => Ty.regionsAt k t ++ Ty.regionsAts k ts
termination_by structural _ ts => ts

def Ty.regionsRow : Nat → List (Nat × List Ty) → List (Nat × Rgn)
  | _, [] => []
  | k, e :: es => Ty.regionsEntry k e ++ Ty.regionsRow k es
termination_by structural _ es => es

def Ty.regionsEntry : Nat → Nat × List Ty → List (Nat × Rgn)
  | k, (_, ts) => Ty.regionsAts k ts
termination_by structural _ e => e

def Ty.regionsEnv : Nat → Option (List Ty) → List (Nat × Rgn)
  | _, none => []
  | k, some ts => Ty.regionsAts k ts
termination_by structural _ env => env

end

theorem Ty.mapRs_eq (f : Nat → Rgn → Rgn) (k : Nat) :
    ∀ ts : List Ty, Ty.mapRs f k ts = ts.map (Ty.mapR f k)
  | [] => by simp [Ty.mapRs]
  | t :: ts => by simp [Ty.mapRs, Ty.mapRs_eq f k ts]

theorem Ty.mapRow_eq (f : Nat → Rgn → Rgn) (k : Nat) :
    ∀ es : List (Nat × List Ty), Ty.mapRow f k es = es.map (Ty.mapEntry f k)
  | [] => by simp [Ty.mapRow]
  | e :: es => by simp [Ty.mapRow, Ty.mapRow_eq f k es]

/-! Applying one function after another is applying their composite. -/

mutual

theorem Ty.mapR_comp (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (t : Ty),
    Ty.mapR f k (Ty.mapR g k t) = Ty.mapR (fun d r => f d (g d r)) k t
  | _, .int => by simp [Ty.mapR]
  | k, .tuple fs => by simp [Ty.mapR, Ty.mapRs_comp f g k fs]
  | k, .data n args => by simp [Ty.mapR, Ty.mapRs_comp f g k args]
  | k, .fn n ps r e once env acc => by
    simp [Ty.mapR, Ty.mapRs_comp f g (k + n) ps, Ty.mapR_comp f g (k + n) r,
      Ty.mapRow_comp f g (k + n) e, Ty.mapEnv_comp f g (k + n) env, List.map_map]
  | k, .ref ρ t => by simp [Ty.mapR, Ty.mapR_comp f g k t]
  | _, .never => by simp [Ty.mapR]

theorem Ty.mapRs_comp (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (ts : List Ty),
    Ty.mapRs f k (Ty.mapRs g k ts) = Ty.mapRs (fun d r => f d (g d r)) k ts
  | _, [] => by simp [Ty.mapRs]
  | k, t :: ts => by simp [Ty.mapRs, Ty.mapR_comp f g k t, Ty.mapRs_comp f g k ts]

theorem Ty.mapRow_comp (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (es : List (Nat × List Ty)),
    Ty.mapRow f k (Ty.mapRow g k es) = Ty.mapRow (fun d r => f d (g d r)) k es
  | _, [] => by simp [Ty.mapRow]
  | k, e :: es => by simp [Ty.mapRow, Ty.mapEntry_comp f g k e, Ty.mapRow_comp f g k es]

theorem Ty.mapEntry_comp (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (e : Nat × List Ty),
    Ty.mapEntry f k (Ty.mapEntry g k e) = Ty.mapEntry (fun d r => f d (g d r)) k e
  | k, (op, ts) => by simp [Ty.mapEntry, Ty.mapRs_comp f g k ts]

theorem Ty.mapEnv_comp (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (env : Option (List Ty)),
    Ty.mapEnv f k (Ty.mapEnv g k env) = Ty.mapEnv (fun d r => f d (g d r)) k env
  | _, none => by simp [Ty.mapEnv]
  | k, some ts => by simp [Ty.mapEnv, Ty.mapRs_comp f g k ts]

end

/-! Two functions that agree on the regions of a type do the same to it. -/

mutual

theorem Ty.mapR_ext (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (t : Ty),
    (∀ x, x ∈ Ty.regionsAt k t → f x.1 x.2 = g x.1 x.2) → Ty.mapR f k t = Ty.mapR g k t
  | _, .int, _ => by simp [Ty.mapR]
  | k, .tuple fs, h => by
    simp only [Ty.mapR]
    rw [Ty.mapRs_ext f g k fs (fun x hx => h x (by simpa [Ty.regionsAt] using hx))]
  | k, .data n args, h => by
    simp only [Ty.mapR]
    rw [Ty.mapRs_ext f g k args (fun x hx => h x (by simpa [Ty.regionsAt] using hx))]
  | k, .fn n ps r e once env acc, h => by
    simp only [Ty.regionsAt, List.mem_append, List.mem_map] at h
    simp only [Ty.mapR]
    rw [Ty.mapRs_ext f g (k + n) ps (fun x hx => h x (.inl hx)),
      Ty.mapR_ext f g (k + n) r (fun x hx => h x (.inr (.inl hx))),
      Ty.mapRow_ext f g (k + n) e (fun x hx => h x (.inr (.inr (.inl hx)))),
      Ty.mapEnv_ext f g (k + n) env (fun x hx => h x (.inr (.inr (.inr (.inl hx)))))]
    have hacc : acc.map (f (k + n)) = acc.map (g (k + n)) :=
      List.map_congr_left fun a ha => h (k + n, a) (.inr (.inr (.inr (.inr ⟨a, ha, rfl⟩))))
    rw [hacc]
  | k, .ref ρ t, h => by
    simp only [Ty.mapR]
    rw [Ty.mapR_ext f g k t (fun x hx => h x (by simp [Ty.regionsAt, hx])),
      h (k, ρ) (by simp [Ty.regionsAt])]
  | _, .never, _ => by simp [Ty.mapR]

theorem Ty.mapRs_ext (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (ts : List Ty),
    (∀ x, x ∈ Ty.regionsAts k ts → f x.1 x.2 = g x.1 x.2) → Ty.mapRs f k ts = Ty.mapRs g k ts
  | _, [], _ => by simp [Ty.mapRs]
  | k, t :: ts, h => by
    simp only [Ty.regionsAts, List.mem_append] at h
    simp only [Ty.mapRs]
    rw [Ty.mapR_ext f g k t (fun x hx => h x (.inl hx)),
      Ty.mapRs_ext f g k ts (fun x hx => h x (.inr hx))]

theorem Ty.mapRow_ext (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (es : List (Nat × List Ty)),
    (∀ x, x ∈ Ty.regionsRow k es → f x.1 x.2 = g x.1 x.2) → Ty.mapRow f k es = Ty.mapRow g k es
  | _, [], _ => by simp [Ty.mapRow]
  | k, e :: es, h => by
    simp only [Ty.regionsRow, List.mem_append] at h
    simp only [Ty.mapRow]
    rw [Ty.mapEntry_ext f g k e (fun x hx => h x (.inl hx)),
      Ty.mapRow_ext f g k es (fun x hx => h x (.inr hx))]

theorem Ty.mapEntry_ext (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (e : Nat × List Ty),
    (∀ x, x ∈ Ty.regionsEntry k e → f x.1 x.2 = g x.1 x.2) →
      Ty.mapEntry f k e = Ty.mapEntry g k e
  | k, (op, ts), h => by
    simp only [Ty.mapEntry]
    rw [Ty.mapRs_ext f g k ts (fun x hx => h x (by simpa [Ty.regionsEntry] using hx))]

theorem Ty.mapEnv_ext (f g : Nat → Rgn → Rgn) : ∀ (k : Nat) (env : Option (List Ty)),
    (∀ x, x ∈ Ty.regionsEnv k env → f x.1 x.2 = g x.1 x.2) → Ty.mapEnv f k env = Ty.mapEnv g k env
  | _, none, _ => by simp [Ty.mapEnv]
  | k, some ts, h => by
    simp only [Ty.mapEnv]
    rw [Ty.mapRs_ext f g k ts (fun x hx => h x (by simpa [Ty.regionsEnv] using hx))]

end

/-! A function that changes no region changes no type. -/

mutual

theorem Ty.mapR_id : ∀ (k : Nat) (t : Ty), Ty.mapR (fun _ r => r) k t = t
  | _, .int => by simp [Ty.mapR]
  | k, .tuple fs => by simp [Ty.mapR, Ty.mapRs_id k fs]
  | k, .data n args => by simp [Ty.mapR, Ty.mapRs_id k args]
  | k, .fn n ps r e once env acc => by
    simp [Ty.mapR, Ty.mapRs_id (k + n) ps, Ty.mapR_id (k + n) r, Ty.mapRow_id (k + n) e,
      Ty.mapEnv_id (k + n) env]
  | k, .ref ρ t => by simp [Ty.mapR, Ty.mapR_id k t]
  | _, .never => by simp [Ty.mapR]

theorem Ty.mapRs_id : ∀ (k : Nat) (ts : List Ty), Ty.mapRs (fun _ r => r) k ts = ts
  | _, [] => by simp [Ty.mapRs]
  | k, t :: ts => by simp [Ty.mapRs, Ty.mapR_id k t, Ty.mapRs_id k ts]

theorem Ty.mapRow_id : ∀ (k : Nat) (es : List (Nat × List Ty)),
    Ty.mapRow (fun _ r => r) k es = es
  | _, [] => by simp [Ty.mapRow]
  | k, e :: es => by simp [Ty.mapRow, Ty.mapEntry_id k e, Ty.mapRow_id k es]

theorem Ty.mapEntry_id : ∀ (k : Nat) (e : Nat × List Ty), Ty.mapEntry (fun _ r => r) k e = e
  | k, (op, ts) => by simp [Ty.mapEntry, Ty.mapRs_id k ts]

theorem Ty.mapEnv_id : ∀ (k : Nat) (env : Option (List Ty)),
    Ty.mapEnv (fun _ r => r) k env = env
  | _, none => by simp [Ty.mapEnv]
  | k, some ts => by simp [Ty.mapEnv, Ty.mapRs_id k ts]

end

/-! The regions of a type a function was applied to are that function applied
to its regions. -/

mutual

theorem Ty.regionsAt_mapR (f : Nat → Rgn → Rgn) : ∀ (k : Nat) (t : Ty),
    Ty.regionsAt k (Ty.mapR f k t) = (Ty.regionsAt k t).map fun x => (x.1, f x.1 x.2)
  | _, .int => by simp [Ty.mapR, Ty.regionsAt]
  | k, .tuple fs => by simp [Ty.mapR, Ty.regionsAt, Ty.regionsAts_mapRs f k fs]
  | k, .data n args => by simp [Ty.mapR, Ty.regionsAt, Ty.regionsAts_mapRs f k args]
  | k, .fn n ps r e once env acc => by
    simp [Ty.mapR, Ty.regionsAt, Ty.regionsAts_mapRs f (k + n) ps, Ty.regionsAt_mapR f (k + n) r,
      Ty.regionsRow_mapRow f (k + n) e, Ty.regionsEnv_mapEnv f (k + n) env, List.map_map]
  | k, .ref ρ t => by simp [Ty.mapR, Ty.regionsAt, Ty.regionsAt_mapR f k t]
  | _, .never => by simp [Ty.mapR, Ty.regionsAt]

theorem Ty.regionsAts_mapRs (f : Nat → Rgn → Rgn) : ∀ (k : Nat) (ts : List Ty),
    Ty.regionsAts k (Ty.mapRs f k ts) = (Ty.regionsAts k ts).map fun x => (x.1, f x.1 x.2)
  | _, [] => by simp [Ty.mapRs, Ty.regionsAts]
  | k, t :: ts => by
    simp [Ty.mapRs, Ty.regionsAts, Ty.regionsAt_mapR f k t, Ty.regionsAts_mapRs f k ts]

theorem Ty.regionsRow_mapRow (f : Nat → Rgn → Rgn) : ∀ (k : Nat) (es : List (Nat × List Ty)),
    Ty.regionsRow k (Ty.mapRow f k es) = (Ty.regionsRow k es).map fun x => (x.1, f x.1 x.2)
  | _, [] => by simp [Ty.mapRow, Ty.regionsRow]
  | k, e :: es => by
    simp [Ty.mapRow, Ty.regionsRow, Ty.regionsEntry_mapEntry f k e, Ty.regionsRow_mapRow f k es]

theorem Ty.regionsEntry_mapEntry (f : Nat → Rgn → Rgn) : ∀ (k : Nat) (e : Nat × List Ty),
    Ty.regionsEntry k (Ty.mapEntry f k e)
      = (Ty.regionsEntry k e).map fun x => (x.1, f x.1 x.2)
  | k, (op, ts) => by simp [Ty.mapEntry, Ty.regionsEntry, Ty.regionsAts_mapRs f k ts]

theorem Ty.regionsEnv_mapEnv (f : Nat → Rgn → Rgn) : ∀ (k : Nat) (env : Option (List Ty)),
    Ty.regionsEnv k (Ty.mapEnv f k env) = (Ty.regionsEnv k env).map fun x => (x.1, f x.1 x.2)
  | _, none => by simp [Ty.mapEnv, Ty.regionsEnv]
  | k, some ts => by simp [Ty.mapEnv, Ty.regionsEnv, Ty.regionsAts_mapRs f k ts]

end

/-! A function that does not look at the depth does the same at every depth. -/

mutual

theorem Ty.mapR_const (g : Rgn → Rgn) : ∀ (k k' : Nat) (t : Ty),
    Ty.mapR (fun _ => g) k t = Ty.mapR (fun _ => g) k' t
  | _, _, .int => by simp [Ty.mapR]
  | k, k', .tuple fs => by simp [Ty.mapR, Ty.mapRs_const g k k' fs]
  | k, k', .data n args => by simp [Ty.mapR, Ty.mapRs_const g k k' args]
  | k, k', .fn n ps r e once env acc => by
    simp [Ty.mapR, Ty.mapRs_const g (k + n) (k' + n) ps, Ty.mapR_const g (k + n) (k' + n) r,
      Ty.mapRow_const g (k + n) (k' + n) e, Ty.mapEnv_const g (k + n) (k' + n) env]
  | k, k', .ref ρ t => by simp [Ty.mapR, Ty.mapR_const g k k' t]
  | _, _, .never => by simp [Ty.mapR]

theorem Ty.mapRs_const (g : Rgn → Rgn) : ∀ (k k' : Nat) (ts : List Ty),
    Ty.mapRs (fun _ => g) k ts = Ty.mapRs (fun _ => g) k' ts
  | _, _, [] => by simp [Ty.mapRs]
  | k, k', t :: ts => by simp [Ty.mapRs, Ty.mapR_const g k k' t, Ty.mapRs_const g k k' ts]

theorem Ty.mapRow_const (g : Rgn → Rgn) : ∀ (k k' : Nat) (es : List (Nat × List Ty)),
    Ty.mapRow (fun _ => g) k es = Ty.mapRow (fun _ => g) k' es
  | _, _, [] => by simp [Ty.mapRow]
  | k, k', e :: es => by
    simp [Ty.mapRow, Ty.mapEntry_const g k k' e, Ty.mapRow_const g k k' es]

theorem Ty.mapEntry_const (g : Rgn → Rgn) : ∀ (k k' : Nat) (e : Nat × List Ty),
    Ty.mapEntry (fun _ => g) k e = Ty.mapEntry (fun _ => g) k' e
  | k, k', (op, ts) => by simp [Ty.mapEntry, Ty.mapRs_const g k k' ts]

theorem Ty.mapEnv_const (g : Rgn → Rgn) : ∀ (k k' : Nat) (env : Option (List Ty)),
    Ty.mapEnv (fun _ => g) k env = Ty.mapEnv (fun _ => g) k' env
  | _, _, none => by simp [Ty.mapEnv]
  | k, k', some ts => by simp [Ty.mapEnv, Ty.mapRs_const g k k' ts]

end

/-! ## Instantiating and opening -/

/-- Put regions in place of the region variables of a type. -/
def Ty.inst (θ : List Rgn) (t : Ty) : Ty := Ty.mapR (fun _ r => r.inst θ) 0 t

/-- Put regions in place of those a callable type binds, in one of its parts. -/
def Ty.open (rs : List Rgn) (t : Ty) : Ty := Ty.mapR (fun d r => r.openAt d rs) 0 t

def Row.inst (θ : List Rgn) (e : Row) : Row := Ty.mapRow (fun _ r => r.inst θ) 0 e

def Row.open (rs : List Rgn) (e : Row) : Row := Ty.mapRow (fun d r => r.openAt d rs) 0 e

theorem Ty.inst_inst (θ η : List Rgn) (t : Ty) :
    (t.inst θ).inst η = t.inst (θ.map (Rgn.inst η)) := by
  simp only [Ty.inst, Ty.mapR_comp]
  congr 1
  funext _ r
  exact Rgn.inst_inst θ η r

theorem Row.inst_inst (θ η : List Rgn) (e : Row) :
    (e.inst θ).inst η = e.inst (θ.map (Rgn.inst η)) := by
  simp only [Row.inst, Ty.mapRow_comp]
  congr 1
  funext _ r
  exact Rgn.inst_inst θ η r

theorem Ty.open_inst (rs η : List Rgn) (t : Ty) :
    (t.open rs).inst η = (t.inst η).open (rs.map (Rgn.inst η)) := by
  simp only [Ty.inst, Ty.open, Ty.mapR_comp]
  congr 1
  funext d r
  exact Rgn.openAt_inst d rs η r

theorem Row.open_inst (rs η : List Rgn) (e : Row) :
    (e.open rs).inst η = (e.inst η).open (rs.map (Rgn.inst η)) := by
  simp only [Row.inst, Row.open, Ty.mapRow_comp]
  congr 1
  funext d r
  exact Rgn.openAt_inst d rs η r

theorem Ty.open_nil (t : Ty) : t.open [] = t := by
  have h : (fun d r => Rgn.openAt d [] r) = fun _ r => r := by
    funext d r
    exact Rgn.openAt_nil d r
  simp only [Ty.open, h, Ty.mapR_id]

theorem Row.open_nil (e : Row) : e.open [] = e := by
  have h : (fun d r => Rgn.openAt d [] r) = fun _ r => r := by
    funext d r
    exact Rgn.openAt_nil d r
  simp only [Row.open, h, Ty.mapRow_id]

/-- Instantiating a callable type instantiates its parts. -/
theorem Ty.inst_fn (θ : List Rgn) (n : Nat) (ps : List Ty) (r : Ty) (e : Row) (once : Bool)
    (env : Option (List Ty)) (acc : List Rgn) :
    (Ty.fn n ps r e once env acc).inst θ
      = .fn n (ps.map (Ty.inst θ)) (r.inst θ) (e.inst θ) once (env.map (·.map (Ty.inst θ)))
          (acc.map (Rgn.inst θ)) := by
  simp only [Ty.inst, Row.inst, Ty.mapR]
  rw [Ty.mapRs_const _ (0 + n) 0, Ty.mapR_const _ (0 + n) 0, Ty.mapRow_const _ (0 + n) 0,
    Ty.mapEnv_const _ (0 + n) 0, Ty.mapRs_eq]
  cases env with
  | none =>
    simp only [Ty.mapEnv, Option.map_none]
    rfl
  | some ts =>
    simp only [Ty.mapEnv, Option.map_some, Ty.mapRs_eq]
    rfl

theorem Ty.inst_ref (θ : List Rgn) (ρ : Rgn) (t : Ty) :
    (Ty.ref ρ t).inst θ = .ref (ρ.inst θ) (t.inst θ) := by
  simp [Ty.inst, Ty.mapR]

theorem Ty.inst_tuple (θ : List Rgn) (fs : List Ty) :
    (Ty.tuple fs).inst θ = .tuple (fs.map (Ty.inst θ)) := by
  simp [Ty.inst, Ty.mapR, Ty.mapRs_eq]

theorem Ty.inst_data (θ : List Rgn) (n : Nat) (args : List Ty) :
    (Ty.data n args).inst θ = .data n (args.map (Ty.inst θ)) := by
  simp [Ty.inst, Ty.mapR, Ty.mapRs_eq]

theorem Ty.inst_int (θ : List Rgn) : Ty.int.inst θ = .int := by simp [Ty.inst, Ty.mapR]

theorem Ty.inst_never (θ : List Rgn) : Ty.never.inst θ = .never := by simp [Ty.inst, Ty.mapR]

/-- Opening a callable type that binds no regions opens its parts. -/
theorem Ty.open_fn0 (rs : List Rgn) (ps : List Ty) (r : Ty) (e : Row) (once : Bool)
    (acc : List Rgn) :
    (Ty.fn 0 ps r e once none acc).open rs
      = .fn 0 (ps.map (Ty.open rs)) (r.open rs) (e.open rs) once none
          (acc.map (Rgn.openAt 0 rs)) := by
  simp [Ty.open, Row.open, Ty.mapR, Ty.mapRs_eq, Ty.mapEnv]

theorem Ty.open_ref (rs : List Rgn) (ρ : Rgn) (t : Ty) :
    (Ty.ref ρ t).open rs = .ref (ρ.openAt 0 rs) (t.open rs) := by
  simp [Ty.open, Ty.mapR]

/-- Looking an operation up in an instantiated row. -/
theorem Row.lookup_inst (θ : List Rgn) (op : Nat) : ∀ e : Row,
    (e.inst θ).lookup op = (e.lookup op).map (·.map (Ty.inst θ))
  | [] => by simp [Row.inst, Ty.mapRow]
  | (op', ts) :: es => by
    have ih := Row.lookup_inst θ op es
    simp only [Row.inst] at ih
    simp only [Row.inst, Ty.mapRow, Ty.mapEntry, List.lookup_cons, Ty.mapRs_eq]
    cases h : op == op' with
    | true => simp [Ty.inst]
    | false => simpa using ih

theorem Row.le_inst {a b : Row} (h : Row.le a b) (θ : List Rgn) :
    Row.le (a.inst θ) (b.inst θ) := by
  intro op sig hl
  rw [Row.lookup_inst] at hl ⊢
  cases ha : a.lookup op with
  | none => simp [ha] at hl
  | some s =>
    rw [h op s ha]
    simpa [ha] using hl

/-! ## Types with no dangling bound region, and types of a signature -/

/-- No region of the type is bound outside it. -/
def Ty.lc (t : Ty) : Bool := (Ty.regionsAt 0 t).all fun x => x.2.lcAt x.1

def Row.lc (e : Row) : Bool := (Ty.regionsRow 0 e).all fun x => x.2.lcAt x.1

theorem Rgn.openAt_lc {d : Nat} {r : Rgn} (rs : List Rgn) (h : r.lcAt d = true) :
    r.openAt d rs = r := by
  induction r with
  | var i => rfl
  | bound j =>
    have hj : j < d := by simpa [Rgn.lcAt] using h
    simp [Rgn.openAt, hj]
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr (ih h)
  | or a b iha ihb =>
    simp only [Rgn.lcAt, Bool.and_eq_true] at h
    simp [Rgn.openAt, iha h.1, ihb h.2]

/-- Opening a type none of whose regions is bound outside it changes nothing. -/
theorem Ty.open_lc {t : Ty} (h : t.lc = true) (rs : List Rgn) : t.open rs = t := by
  have := Ty.mapR_ext (fun d r => r.openAt d rs) (fun _ r => r) 0 t fun x hx =>
    Rgn.openAt_lc rs (List.all_eq_true.mp h x hx)
  simp only [Ty.open, this, Ty.mapR_id]

theorem Row.open_lc {e : Row} (h : e.lc = true) (rs : List Rgn) : e.open rs = e := by
  have := Ty.mapRow_ext (fun d r => r.openAt d rs) (fun _ r => r) 0 e fun x hx =>
    Rgn.openAt_lc rs (List.all_eq_true.mp h x hx)
  simp only [Row.open, this, Ty.mapRow_id]

theorem Ty.lc_inst {t : Ty} (h : t.lc = true) (θ : List Rgn) : (t.inst θ).lc = true := by
  simp only [Ty.lc, Ty.inst, Ty.regionsAt_mapR, List.all_map] at h ⊢
  exact List.all_eq_true.mpr fun x hx => Rgn.lcAt_inst (List.all_eq_true.mp h x hx) θ

theorem Row.lc_inst {e : Row} (h : e.lc = true) (θ : List Rgn) : (e.inst θ).lc = true := by
  simp only [Row.lc, Row.inst, Ty.regionsRow_mapRow, List.all_map] at h ⊢
  exact List.all_eq_true.mpr fun x hx => Rgn.lcAt_inst (List.all_eq_true.mp h x hx) θ

/-- Every region variable of the type is below `c`. -/
def Ty.within (c : Nat) (t : Ty) : Bool := (Ty.regionsAt 0 t).all fun x => x.2.within c

def Row.within (c : Nat) (e : Row) : Bool := (Ty.regionsRow 0 e).all fun x => x.2.within c

theorem Rgn.inst_append {θ : List Rgn} {r : Rgn} (h : r.within θ.length = true) (rs : List Rgn) :
    r.inst (θ ++ rs) = r.inst θ := by
  induction r with
  | var i =>
    have hi : i < θ.length := by simpa [Rgn.within] using h
    show Rgn.clean (θ ++ rs)[i]? = Rgn.clean θ[i]?
    rw [List.getElem?_append_left hi]
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr (ih h)
  | or a b iha ihb =>
    simp only [Rgn.within, Bool.and_eq_true] at h
    simp [Rgn.inst, iha h.1, ihb h.2]

theorem Ty.inst_append {θ : List Rgn} {t : Ty} (h : t.within θ.length = true) (rs : List Rgn) :
    t.inst (θ ++ rs) = t.inst θ :=
  Ty.mapR_ext _ _ 0 t fun x hx => Rgn.inst_append (List.all_eq_true.mp h x hx) rs

/-- The type of a signature, seen from the body: its call regions opened to
variables, then everything instantiated as the function was entered. -/
theorem Ty.open_callVars_inst {θ : List Rgn} {t : Ty} (h : t.within θ.length = true)
    (rs : List Rgn) :
    (t.open (Rgn.callVars θ.length rs.length)).inst (θ ++ rs) = (t.inst θ).open rs := by
  simp only [Ty.inst, Ty.open, Ty.mapR_comp]
  exact Ty.mapR_ext _ _ 0 t fun x hx =>
    Rgn.open_callVars_inst x.1 θ rs x.2 (List.all_eq_true.mp h x hx)

theorem Row.open_callVars_inst {θ : List Rgn} {e : Row} (h : e.within θ.length = true)
    (rs : List Rgn) :
    (e.open (Rgn.callVars θ.length rs.length)).inst (θ ++ rs) = (e.inst θ).open rs := by
  simp only [Row.inst, Row.open, Ty.mapRow_comp]
  exact Ty.mapRow_ext _ _ 0 e fun x hx =>
    Rgn.open_callVars_inst x.1 θ rs x.2 (List.all_eq_true.mp h x hx)

/-! ## The shape of a type, and its regions

A declared type is looked up by the shape of its arguments: the arguments with
every region that is not bound taken out. What the declaration says of that
shape is said in terms of those regions, numbered in order; `frees` gives them
back. Instantiating region variables changes neither the shape nor the order.
-/

/-- A region that is not bound, forgotten. Leave to write stays leave to write. -/
def Rgn.shape : Rgn → Rgn
  | .wr r => .wr r.shape
  | .var _ => .cell 0
  | .bound k => .bound k
  | .cell _ => .cell 0
  | .lab _ => .cell 0
  | .loan _ => .cell 0
  | .or a b => if a.free && b.free then .cell 0 else .or a.shape b.shape

def Rgn.isWr : Rgn → Bool
  | .wr _ => true
  | _ => false

theorem Rgn.place_shape {r : Rgn} (h : r.place = true) : r.shape = .cell 0 := by
  cases r with
  | bound k => cases h
  | wr r => cases h
  | or a b =>
    simp only [Rgn.place, Bool.and_eq_true] at h
    simp [Rgn.shape, Rgn.place_free h.1, Rgn.place_free h.2]
  | _ => rfl

theorem Rgn.clean_shape (o : Option Rgn) : (Rgn.clean o).shape = .cell 0 :=
  Rgn.place_shape (Rgn.clean_place o)

theorem Rgn.clean_isWr (o : Option Rgn) : (Rgn.clean o).isWr = false := by
  have h := Rgn.clean_place o
  cases hc : Rgn.clean o with
  | wr r => rw [hc] at h; cases h
  | _ => rfl

theorem Rgn.shape_inst (θ : List Rgn) (r : Rgn) : (r.inst θ).shape = r.shape := by
  induction r with
  | var i => exact Rgn.clean_shape _
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih
  | or a b iha ihb =>
    simp only [Rgn.inst, Rgn.shape, Rgn.inst_free, iha, ihb]

theorem Rgn.isWr_inst (θ : List Rgn) (r : Rgn) : (r.inst θ).isWr = r.isWr := by
  cases r with
  | var i => exact Rgn.clean_isWr _
  | _ => rfl

/-- A type with every region that is not bound replaced by the same one. -/
def Ty.shape (t : Ty) : Ty := Ty.mapR (fun _ r => r.shape) 0 t

/-- The regions of a type that are not bound, in order. Leave to write a region
is not a region of its own: it is written in terms of the region. -/
def Ty.frees (t : Ty) : List Rgn :=
  ((Ty.regionsAt 0 t).map (·.2)).filter fun r => r.free && !r.isWr

theorem Ty.shape_inst (θ : List Rgn) (t : Ty) : (t.inst θ).shape = t.shape := by
  simp only [Ty.shape, Ty.inst, Ty.mapR_comp]
  congr 1
  funext _ r
  exact Rgn.shape_inst θ r

theorem Ty.frees_inst (θ : List Rgn) (t : Ty) : (t.inst θ).frees = t.frees.map (Rgn.inst θ) := by
  simp only [Ty.frees, Ty.inst, Ty.regionsAt_mapR, List.map_map, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  show ((Rgn.inst θ x.2).free && !(Rgn.inst θ x.2).isWr) = (x.2.free && !x.2.isWr)
  rw [Rgn.inst_free, Rgn.isWr_inst]

end Glorious.Typing
