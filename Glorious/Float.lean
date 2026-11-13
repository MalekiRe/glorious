/-!
# Floating point, written out

A floating point number is held by both machines as the integer whose bits are
its IEEE 754 encoding. What the arithmetic on those bits means is defined
here, exactly, on natural numbers: each operation is the true result rounded
to the nearest number that can be held, a tie going to the one whose last bit
is zero. Nothing here is Lean's `Float`, which the kernel cannot compute with.

Every operation that would give a NaN gives the one quiet NaN with no sign and
no payload, so that a program cannot tell two machines apart by one.
-/

namespace Glorious.Ieee

/-- A format: the bits of its significand, the exponent of the last bit of its
smallest numbers, and the bits of its exponent field. -/
structure Format where
  prec : Nat
  emin : Int
  expBits : Nat

def binary64 : Format := ⟨53, -1074, 11⟩

def binary32 : Format := ⟨24, -149, 8⟩

/-- What an encoding stands for. A finite number is `m * 2^e`, with a sign;
zero has a sign too. -/
inductive Num where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)

/-- The bits of a 64-bit integer, as a natural number. -/
def toBits (x : Int) : Nat := (x % 18446744073709551616).toNat

/-- The 64-bit integer with these bits. -/
def ofBits (n : Nat) : Int :=
  let n := n % 18446744073709551616
  if n < 9223372036854775808 then (n : Int) else (n : Int) - 18446744073709551616

def Format.fracBits (f : Format) : Nat := f.prec - 1

def Format.signBit (f : Format) (neg : Bool) : Nat :=
  if neg then 2 ^ (f.fracBits + f.expBits) else 0

def Format.infBits (f : Format) (neg : Bool) : Nat :=
  f.signBit neg + (2 ^ f.expBits - 1) * 2 ^ f.fracBits

def Format.nanBits (f : Format) : Nat :=
  (2 ^ f.expBits - 1) * 2 ^ f.fracBits + 2 ^ (f.fracBits - 1)

def Format.zeroBits (f : Format) (neg : Bool) : Nat := f.signBit neg

def Format.decode (f : Format) (bits : Nat) : Num :=
  let frac := bits % 2 ^ f.fracBits
  let expf := (bits / 2 ^ f.fracBits) % 2 ^ f.expBits
  let neg := (bits / 2 ^ (f.fracBits + f.expBits)) % 2 == 1
  if expf == 2 ^ f.expBits - 1 then (if frac == 0 then .inf neg else .nan)
  else if expf == 0 then .fin neg frac f.emin
  else .fin neg (frac + 2 ^ f.fracBits) (f.emin + ((expf : Int) - 1))

/-- `n / d * 2^e` divided by `2^at_`, as a whole number and what is left over,
with what the left over is a part of. -/
def scaled (n d : Nat) (e at_ : Int) : Nat × Nat × Nat :=
  if e ≥ at_ then
    let n := n * 2 ^ (e - at_).toNat
    (n / d, n % d, d)
  else
    let d := d * 2 ^ (at_ - e).toNat
    (n / d, n % d, d)

/-- A whole number and a left over, to the nearest whole number: a half goes
to the even one. -/
def nearest (q r d : Nat) : Nat :=
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- The encoding of `n / d * 2^e`, with a sign, rounded to the format. `n` and
`d` are not zero. Too large is infinity. -/
def Format.round (f : Format) (neg : Bool) (n d : Nat) (e : Int) : Nat :=
  -- `n / d * 2^e` is between `2^(l-1)` and `2^(l+1)`.
  let l : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int) + e
  let e0 := l - f.prec
  let e1 := if (scaled n d e e0).1 ≥ 2 ^ f.prec then e0 + 1 else e0
  let e2 := if e1 < f.emin then f.emin else e1
  let (q, r, den) := scaled n d e e2
  let m := nearest q r den
  let (m, e2) := if m ≥ 2 ^ f.prec then (2 ^ f.fracBits, e2 + 1) else (m, e2)
  if m < 2 ^ f.fracBits then f.signBit neg + m
  else
    let expf := (e2 - f.emin + 1).toNat
    if expf ≥ 2 ^ f.expBits - 1 then f.infBits neg
    else f.signBit neg + expf * 2 ^ f.fracBits + (m - 2 ^ f.fracBits)

/-- The encoding of a number, exactly if the format can hold it. -/
def Format.encode (f : Format) : Num → Nat
  | .nan => f.nanBits
  | .inf neg => f.infBits neg
  | .fin neg m e => if m == 0 then f.zeroBits neg else f.round neg m 1 e

/-- A finite number as a whole number of `2^at_`, where `at_` is not above its
exponent. -/
def aligned (neg : Bool) (m : Nat) (e at_ : Int) : Int :=
  let v : Int := (m * 2 ^ (e - at_).toNat : Nat)
  if neg then -v else v

def add (f : Format) : Num → Num → Nat
  | .nan, _ => f.nanBits
  | _, .nan => f.nanBits
  | .inf s, .inf t => if s == t then f.infBits s else f.nanBits
  | .inf s, .fin _ _ _ => f.infBits s
  | .fin _ _ _, .inf t => f.infBits t
  | .fin s m e, .fin t n k =>
    let at_ := if e ≤ k then e else k
    let sum := aligned s m e at_ + aligned t n k at_
    -- A sum that is exactly zero is negative only if both parts are.
    if sum.natAbs == 0 then f.zeroBits (s && t) else f.round (sum < 0) sum.natAbs 1 at_

def neg : Num → Num
  | .nan => .nan
  | .inf s => .inf (!s)
  | .fin s m e => .fin (!s) m e

def mul (f : Format) : Num → Num → Nat
  | .nan, _ => f.nanBits
  | _, .nan => f.nanBits
  | .inf s, .inf t => f.infBits (s != t)
  | .inf s, .fin t n _ => if n == 0 then f.nanBits else f.infBits (s != t)
  | .fin s m _, .inf t => if m == 0 then f.nanBits else f.infBits (s != t)
  | .fin s m e, .fin t n k =>
    if m == 0 || n == 0 then f.zeroBits (s != t) else f.round (s != t) (m * n) 1 (e + k)

def div (f : Format) : Num → Num → Nat
  | .nan, _ => f.nanBits
  | _, .nan => f.nanBits
  | .inf _, .inf _ => f.nanBits
  | .inf s, .fin t _ _ => f.infBits (s != t)
  | .fin s _ _, .inf t => f.zeroBits (s != t)
  | .fin s m e, .fin t n k =>
    if n == 0 then (if m == 0 then f.nanBits else f.infBits (s != t))
    else if m == 0 then f.zeroBits (s != t)
    else f.round (s != t) m n (e - k)

/-- Is the first number smaller? Never, if either is a NaN. -/
def lt : Num → Num → Bool
  | .nan, _ => false
  | _, .nan => false
  | .inf s, .inf t => s && !t
  | .inf s, .fin _ _ _ => s
  | .fin _ _ _, .inf t => !t
  | .fin s m e, .fin t n k =>
    let at_ := if e ≤ k then e else k
    aligned s m e at_ < aligned t n k at_

/-- Are the numbers equal? Never, if either is a NaN; the two zeros are. -/
def eq : Num → Num → Bool
  | .nan, _ => false
  | _, .nan => false
  | .inf s, .inf t => s == t
  | .inf _, .fin _ _ _ => false
  | .fin _ _ _, .inf _ => false
  | .fin s m e, .fin t n k =>
    let at_ := if e ≤ k then e else k
    decide (aligned s m e at_ = aligned t n k at_)

/-- The number nearest a whole number. -/
def ofInt (f : Format) (n : Int) : Nat :=
  if n.natAbs == 0 then f.zeroBits false else f.round (n < 0) n.natAbs 1 0

/-- A number without what is after its point; none for infinity and NaN. -/
def toInt : Num → Option Int
  | .nan => none
  | .inf _ => none
  | .fin s m e =>
    let whole : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    some (if s then -(whole : Int) else whole)

/-- `digits * 10^exp10`, to the nearest number of the format. -/
def ofDecimal (f : Format) (digits exp10 : Int) : Nat :=
  if digits.natAbs == 0 then f.zeroBits false
  else if exp10 > 400 then f.infBits (digits < 0)
  else if exp10 < -400 then f.zeroBits (digits < 0)
  else if exp10 ≥ 0 then f.round (digits < 0) (digits.natAbs * 10 ^ exp10.toNat) 1 0
  else f.round (digits < 0) digits.natAbs (10 ^ (-exp10).toNat) 0

/-- `m * 2^e / 10^k` to the nearest whole number. -/
def decimalAt (m : Nat) (e k : Int) : Nat :=
  let n := if e ≥ 0 then m * 2 ^ e.toNat else m
  let d := if e ≥ 0 then 1 else 2 ^ (-e).toNat
  let n := if k < 0 then n * 10 ^ (-k).toNat else n
  let d := if k ≥ 0 then d * 10 ^ k.toNat else d
  nearest (n / d) (n % d) d

/-- The `k` at which `m * 2^e / 10^k`, to the nearest whole number, has
exactly `p` digits, looked for from a guess. -/
def settle (m : Nat) (e : Int) (p : Nat) : Nat → Int → Nat × Int
  | 0, k => (decimalAt m e k, k)
  | fuel + 1, k =>
    let d := decimalAt m e k
    if d ≥ 10 ^ p then settle m e p fuel (k + 1)
    else if d < 10 ^ (p - 1) then settle m e p fuel (k - 1)
    else (d, k)

/-- A number to `p` digits: the digits as a whole number `d` and the `k` with
`d * 10^k` nearest the number, its sign left out. Zero is `(0, 0)`. None for
infinity and NaN, or if `p` is not from 1 to 17. -/
def decimal (x : Num) (p : Nat) : Option (Nat × Int) :=
  if p == 0 || p > 17 then none
  else
    match x with
    | .nan => none
    | .inf _ => none
    | .fin _ m e =>
      if m == 0 then some (0, 0)
      else
        -- About where the first digit is: `log10 2` is near 0.30103.
        let guess : Int := ((Nat.log2 m : Int) + e) * 30103 / 100000
        some (settle m e p 8 (guess - (p : Int) + 1))

/-- The square root, to the nearest number of the format. -/
def sqrt (f : Format) : Num → Nat
  | .nan => f.nanBits
  | .inf neg => if neg then f.nanBits else f.infBits false
  | .fin neg m e =>
    if m == 0 then f.zeroBits neg
    else if neg then f.nanBits
    else
      -- `m * 2^e` as `n * 2^(2k)` with `n` large enough that its whole
      -- square root has two bits more than the format keeps; what the whole
      -- root leaves out is one more bit, set if anything is left out.
      let shift : Nat := 2 * (f.prec + 2) + (e % 2).toNat
      let n := m * 2 ^ shift
      let root := Nat.sqrt n
      let rest := if root * root == n then 0 else 1
      f.round false (2 * root + rest) 2 ((e - (shift : Int)) / 2)

/-- A number without what is after its point, the way `mode` says: 0 down, 1
up, 2 towards zero, 3 to the nearest, a half to the even one. None for any
other `mode`. -/
def roundWhole (f : Format) (mode : Int) : Num → Option Nat
  | .nan => some f.nanBits
  | .inf neg => some (f.infBits neg)
  | .fin neg m e =>
    if e ≥ 0 then some (if m == 0 then f.zeroBits neg else f.round neg m 1 e)
    else
      let d := 2 ^ (-e).toNat
      let q := m / d
      let r := m % d
      let whole : Option Nat :=
        if mode.natAbs == 0 then some (if neg && r > 0 then q + 1 else q)
        else if mode.natAbs == 1 && mode ≥ 0 then some (if !neg && r > 0 then q + 1 else q)
        else if mode.natAbs == 2 && mode ≥ 0 then some q
        else if mode.natAbs == 3 && mode ≥ 0 then some (nearest q r d)
        else none
      whole.map fun w => if w == 0 then f.zeroBits neg else f.round neg w 1 0

/-! The operations on encodings, as both machines have them: integers in,
an integer out. -/

def f64 (bits : Int) : Num := binary64.decode (toBits bits)

def f64Add (a b : Int) : Int := ofBits (add binary64 (f64 a) (f64 b))

def f64Sub (a b : Int) : Int := ofBits (add binary64 (f64 a) (neg (f64 b)))

def f64Mul (a b : Int) : Int := ofBits (mul binary64 (f64 a) (f64 b))

def f64Div (a b : Int) : Int := ofBits (div binary64 (f64 a) (f64 b))

def f64Lt (a b : Int) : Int := if lt (f64 a) (f64 b) then 1 else 0

def f64Eq (a b : Int) : Int := if eq (f64 a) (f64 b) then 1 else 0

def f64OfInt (n : Int) : Int := ofBits (ofInt binary64 n)

def f64ToInt (a : Int) : Option Int := toInt (f64 a)

/-- The encoding in 32 bits of the number nearest a 64-bit one. -/
def f64Narrow (a : Int) : Int := ofBits (binary32.encode (f64 a))

/-- The 64-bit encoding of a number held in 32 bits. -/
def f64Widen (a : Int) : Int := ofBits (binary64.encode (binary32.decode (toBits a % 4294967296)))

def f64OfDecimal (digits exp10 : Int) : Int := ofBits (ofDecimal binary64 digits exp10)

def f64Sqrt (a : Int) : Int := ofBits (sqrt binary64 (f64 a))

def f64Round (a mode : Int) : Option Int := (roundWhole binary64 mode (f64 a)).map ofBits

def f64Digits (a p : Int) : Option Int :=
  if p < 0 then none else (decimal (f64 a) p.toNat).map fun (d, _) => (d : Int)

def f64Exp10 (a p : Int) : Option Int :=
  if p < 0 then none else (decimal (f64 a) p.toNat).map fun (_, k) => k

end Glorious.Ieee
