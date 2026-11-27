/-!
# Computational definitions (no Mathlib)

The definitions evaluated by `decide +kernel` in the large chunked verification. This file
deliberately imports nothing beyond core Lean, so that the many generated chunk files start
quickly and use little memory. Soundness proofs live in `Collatz.Residue`, `Collatz.Kernel`
and `Collatz.CycleBound`.
-/

namespace Collatz

/-- One symbolic step on the affine form `a * m + b` (valid when `a` is even). -/
def next (a b : Nat) : Nat × Nat := if b % 2 = 0 then (a / 2, b / 2) else (3 * a, 3 * b + 1)

/-- Symbolic run with fuel, checking for a certificate of descent. -/
def certAux (K r : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if a % 2 = 0 then
      if (next a b).1 < K ∧ (next a b).2 ≤ r then true
      else certAux K r fuel (next a b).1 (next a b).2
    else false

/-- `cert k r = true` certifies that every `n ≥ 2^k` with `n % 2^k = r` descends. -/
def cert (k r : Nat) : Bool := certAux (2 ^ k) r (2 * k + 1) (2 ^ k) r

/-- Accelerated Collatz step: `n / 2` if even, `(3n + 1) / 2` if odd. -/
def kstepT (n : Nat) : Nat := bif n % 2 == 0 then n / 2 else (3 * n + 1) / 2

/-- Does the orbit of `x` drop below `n0` within `fuel` accelerated steps? -/
def kdesc (n0 fuel x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ rec x => (kstepT x).blt n0 || rec (kstepT x)) fuel x

/-- `kall f n = true` iff `f i = true` for all `i < n`. -/
def kall (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => f i && acc) n

/-- `kallFrom f lo len = true` iff `f i = true` for all `lo ≤ i < lo + len`. -/
def kallFrom (f : Nat → Bool) (lo len : Nat) : Bool := kall (fun i => f (lo + i)) len

/-- Residue check: either `r` is certified (and `r` itself descends), or every
`n = 2^k m + r` with `m < M` is checked directly. -/
def resCheck (k M fuel r : Nat) : Bool :=
  (cert k r && (r.blt 2 || kdesc r fuel r)) ||
    kall (fun m => (2 ^ k * m + r).blt 2 || kdesc (2 ^ k * m + r) fuel (2 ^ k * m + r)) M

/-- Lower convergent of `log₂ 3`: `2^LP < 3^LQ`. -/
def LP : Nat := 176251
def LQ : Nat := 111202
/-- Upper convergent of `log₂ 3`: `3^UQ < 2^UP`. -/
def UP : Nat := 301994
def UQ : Nat := 190537
/-- `κ = KN / KD > 1 / log 2`. -/
def KN : Nat := 10000000000
def KD : Nat := 6931471803

/-- Cheap check that no cycle has `b` odd steps with all odd elements `≥ N`. -/
def cycCheck2 (N b : Nat) : Bool :=
  b == 0 || Nat.ble (b * (UP * (3 * N) * KD + KN * UQ)) ((UQ * (3 * N) * KD) * (b * LP / LQ + 1))

end Collatz
