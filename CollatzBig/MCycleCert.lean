/-!
# Kernel certificates for `CollatzBig.MCycle`

Integer inequalities checked by `decide +kernel` (numerals of at most `2.8 · 10^8` bits):

* `upM`: `(M + 1) 3^d ≤ M 2^c`, i.e. `2^c / 3^d ≥ 1 + 1/M`, for the upper fractions `c/d` used
  with at most `13, 38, 63, 88, 469` odd blocks;
* `low38`, `low469`: `2^a < 3^b` for the lower fractions `85137581/53715833` and
  `16785921/10590737` (`357638239/225644606` comes from `CollatzBig.CircuitCert.lowA`).

As in `CollatzBig.CircuitCert`, exponents are written `1048576 * q + r` and split with
`Nat.pow_add`, `Nat.pow_mul` (the kernel refuses `Nat.pow` results it estimates above 128 MB),
and every statement is quantified over a `p` equal to `^`. Parameters: `scripts/mcycle_cert.py`.
This module imports nothing.
-/

namespace CollatzBig.MCycleCert

/-- `558903957 * 3^171928773 ≤ 558903956 * 2^272500658` (at most `13` blocks). -/
theorem up13 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (558903956 + 1) * p 3 (1048576 * 163 + 1010885) ≤ 558903956 * p 2 (1048576 * 259 + 919474) := by
  rw [hp, hp]
  rw [Nat.pow_add 3 (1048576 * 163) 1010885, Nat.pow_mul 3 1048576 163,
    Nat.pow_add 2 (1048576 * 259) 919474, Nat.pow_mul 2 1048576 259]
  decide +kernel

/-- `190048851 * 3^118212940 ≤ 190048850 * 2^187363077` (at most `38` blocks). -/
theorem up38 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (190048850 + 1) * p 3 (1048576 * 112 + 772428) ≤ 190048850 * p 2 (1048576 * 178 + 716549) := by
  rw [hp, hp]
  rw [Nat.pow_add 3 (1048576 * 112) 772428, Nat.pow_mul 3 1048576 112,
    Nat.pow_add 2 (1048576 * 178) 716549, Nat.pow_mul 2 1048576 178]
  decide +kernel

/-- `114489914 * 3^64497107 ≤ 114489913 * 2^102225496` (at most `63` blocks). -/
theorem up63 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (114489913 + 1) * p 3 (1048576 * 61 + 533971) ≤ 114489913 * p 2 (1048576 * 97 + 513624) := by
  rw [hp, hp]
  rw [Nat.pow_add 3 (1048576 * 61) 533971, Nat.pow_mul 3 1048576 61,
    Nat.pow_add 2 (1048576 * 97) 513624, Nat.pow_mul 2 1048576 97]
  decide +kernel

/-- `81920326 * 3^10781274 ≤ 81920325 * 2^17087915` (at most `88` blocks). -/
theorem up88 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (81920325 + 1) * p 3 (1048576 * 10 + 295514) ≤ 81920325 * p 2 (1048576 * 16 + 310699) := by
  rw [hp, hp]
  rw [Nat.pow_add 3 (1048576 * 10) 295514, Nat.pow_mul 3 1048576 10,
    Nat.pow_add 2 (1048576 * 16) 310699, Nat.pow_mul 2 1048576 16]
  decide +kernel

/-- `15502074 * 3^190537 ≤ 15502073 * 2^301994` (at most `469` blocks). -/
theorem up469 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (15502073 + 1) * p 3 190537 ≤ 15502073 * p 2 301994 := by
  rw [hp, hp]
  decide +kernel

/-- `2^85137581 < 3^53715833`. -/
theorem low38 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    p 2 (1048576 * 81 + 202925) < p 3 (1048576 * 51 + 238457) := by
  rw [hp, hp]
  rw [Nat.pow_add 2 (1048576 * 81) 202925, Nat.pow_mul 2 1048576 81,
    Nat.pow_add 3 (1048576 * 51) 238457, Nat.pow_mul 3 1048576 51]
  decide +kernel

/-- `2^16785921 < 3^10590737`. -/
theorem low469 (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    p 2 (1048576 * 16 + 8705) < p 3 (1048576 * 10 + 104977) := by
  rw [hp, hp]
  rw [Nat.pow_add 2 (1048576 * 16) 8705, Nat.pow_mul 2 1048576 16,
    Nat.pow_add 3 (1048576 * 10) 104977, Nat.pow_mul 3 1048576 10]
  decide +kernel

end CollatzBig.MCycleCert
