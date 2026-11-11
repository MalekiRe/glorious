import Glorious.Core.Semantics

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

/-- Is this region not one bound by a callable type? -/
def free : Rgn → Bool
  | .bound _ => false
  | .var _ => true
  | .cell _ => true
  | .lab _ => true
  | .loan _ => true
  | .wr r => r.free

/-- A region to put in place of another: never one that would be bound where
it lands, and a place, not a permission. -/
def clean : Option Rgn → Rgn
  | some (.bound _) => .cell 0
  | some (.wr _) => .cell 0
  | some r => r
  | none => .cell 0

/-- Put regions in place of a function's region variables. -/
def inst (θ : List Rgn) : Rgn → Rgn
  | .var i => clean θ[i]?
  | .wr r => .wr (inst θ r)
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
  | r => r

theorem clean_free (o : Option Rgn) : (clean o).free = true := by
  cases o with
  | none => rfl
  | some r => cases r <;> rfl

theorem clean_clean (o : Option Rgn) : clean (some (clean o)) = clean o := by
  cases o with
  | none => rfl
  | some r => cases r <;> rfl

theorem inst_free (θ : List Rgn) (r : Rgn) : (r.inst θ).free = r.free := by
  induction r with
  | var i => exact clean_free _
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact ih

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

/-- Instantiating twice is instantiating once, by the regions instantiated. -/
theorem inst_inst (θ η : List Rgn) (r : Rgn) :
    (r.inst θ).inst η = r.inst (θ.map (inst η)) := by
  induction r with
  | var i =>
    show (clean θ[i]?).inst η = clean ((θ.map (inst η))[i]?)
    rw [List.getElem?_map]
    cases h : θ[i]? with
    | none => rfl
    | some x =>
      cases x with
      | var j => exact (clean_clean _).symm
      | bound k => rfl
      | cell a => rfl
      | lab id => rfl
      | loan b => rfl
      | wr y => rfl
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih

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
        rw [hl, hr]
        cases x with
        | var i => exact (clean_clean _).symm
        | bound k => rfl
        | cell a => rfl
        | lab id => rfl
        | loan b => rfl
        | wr y => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih

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
          simp [openAt, hj, h1, clean]
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

/-- A region that is bound is left as it is. -/
theorem inst_bound {r : Rgn} (h : r.free = false) (θ : List Rgn) : r.inst θ = r := by
  induction r with
  | var i => cases h
  | bound k => rfl
  | cell a => cases h
  | lab id => cases h
  | loan b => cases h
  | wr r ih => exact congrArg Rgn.wr (ih h)

/-- No part of the region is bound more than `d` callable types out. -/
def lcAt (d : Nat) : Rgn → Bool
  | .bound j => decide (j < d)
  | .wr r => lcAt d r
  | _ => true

theorem lcAt_inst {d : Nat} {r : Rgn} (h : r.lcAt d = true) (θ : List Rgn) :
    (r.inst θ).lcAt d = true := by
  induction r with
  | var i =>
    have := clean_free θ[i]?
    show (clean θ[i]?).lcAt d = true
    cases hc : clean θ[i]? with
    | bound k => rw [hc] at this; cases this
    | wr y =>
      cases hθ : θ[i]? with
      | none => rw [hθ] at hc; cases hc
      | some x => rw [hθ] at hc; cases x <;> cases hc
    | _ => rfl
  | bound k => exact h
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact ih h

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

def Rgn.isWr : Rgn → Bool
  | .wr _ => true
  | _ => false

theorem Rgn.clean_shape (o : Option Rgn) : (Rgn.clean o).shape = .cell 0 := by
  cases o with
  | none => rfl
  | some r => cases r <;> rfl

theorem Rgn.clean_isWr (o : Option Rgn) : (Rgn.clean o).isWr = false := by
  cases o with
  | none => rfl
  | some r => cases r <;> rfl

theorem Rgn.shape_inst (θ : List Rgn) (r : Rgn) : (r.inst θ).shape = r.shape := by
  induction r with
  | var i => exact Rgn.clean_shape _
  | bound k => rfl
  | cell a => rfl
  | lab id => rfl
  | loan b => rfl
  | wr r ih => exact congrArg Rgn.wr ih

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
