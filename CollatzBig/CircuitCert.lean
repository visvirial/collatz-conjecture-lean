/-!
# Kernel certificates for `CollatzBig.Circuit`

Four inequalities between integers of up to 630 million bits, checked by `decide +kernel`
(GMP arithmetic in the kernel). With

* `a / b = 357638239 / 225644606` (lower convergent of `log₂ 3`),
* `c / d = 630138897 / 397573379` (the next upper convergent),
* `N = 7281311744` (`CollatzBig.Ext.descends_below`),

they state:

* `lowA`:   `2^a / 3^b ≤ 1 - 1/594045519`;
* `upR`:    `2^c / 3^d ≤ 1 + 1/9447912334`;
* `upN`:    `2^c / 3^d ≥ 1 + 1/(2N)`;
* `notDvd`: `2^c - 3^d` does not divide `3^d - 2^d`
  (the quotient would be `≈ 9447912335.13`).

The kernel refuses `Nat.pow` with an exponent above `2^24`, and numerals above `2^30` bits.
So every exponent is written as `1048576 * q + r` and split with `Nat.pow_add` and
`Nat.pow_mul`; the largest numeral has about `6.3 · 10^8` bits. This module imports nothing,
so it can be compiled once with `lean -o` (about 20 s and 1.4 GB in total).
-/

namespace CollatzBig.CircuitCert

/-! Each statement is universally quantified over a function `p` equal to `^`, so that it can be
transported to Mathlib's `Monoid.npow` instance (`CollatzBig.Circuit`) by a defeq check under the
binder `p`: a kernel defeq check between two different closed forms of these numbers would try to
evaluate `3 ^ 397573379` in one step and fail. -/

/-- `594045519 * 2^357638239 ≤ 594045518 * 3^225644606`. -/
theorem lowA (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    594045519 * p 2 (1048576 * 341 + 73823)
    ≤ (594045519 - 1) * p 3 (1048576 * 215 + 200766) := by
  rw [hp, hp]
  rw [Nat.pow_add 2 (1048576 * 341) 73823, Nat.pow_mul 2 1048576 341,
    Nat.pow_add 3 (1048576 * 215) 200766, Nat.pow_mul 3 1048576 215]
  decide +kernel

/-- `9447912334 * 2^630138897 ≤ 9447912335 * 3^397573379`. -/
theorem upR (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    9447912334 * p 2 (1048576 * 600 + 993297)
    ≤ (9447912334 + 1) * p 3 (1048576 * 379 + 163075) := by
  rw [hp, hp]
  rw [Nat.pow_add 2 (1048576 * 600) 993297, Nat.pow_mul 2 1048576 600,
    Nat.pow_add 3 (1048576 * 379) 163075, Nat.pow_mul 3 1048576 379]
  decide +kernel

/-- `(2N + 1) * 3^397573379 ≤ 2N * 2^630138897` with `N = 7281311744`. -/
theorem upN (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (2 * 7281311744 + 1) * p 3 (1048576 * 379 + 163075)
    ≤ 2 * 7281311744 * p 2 (1048576 * 600 + 993297) := by
  rw [hp, hp]
  rw [Nat.pow_add 3 (1048576 * 379) 163075, Nat.pow_mul 3 1048576 379,
    Nat.pow_add 2 (1048576 * 600) 993297, Nat.pow_mul 2 1048576 600]
  decide +kernel

/-- `(3^397573379 - 2^397573379) % (2^630138897 - 3^397573379) ≠ 0`. -/
theorem notDvd (p : Nat → Nat → Nat) (hp : ∀ a b, p a b = a ^ b) :
    (p 3 (1048576 * 379 + 163075) - p 2 (1048576 * 379 + 163075))
    % (p 2 (1048576 * 600 + 993297) - p 3 (1048576 * 379 + 163075)) ≠ 0 := by
  rw [hp, hp, hp]
  rw [Nat.pow_add 3 (1048576 * 379) 163075, Nat.pow_mul 3 1048576 379,
    Nat.pow_add 2 (1048576 * 379) 163075, Nat.pow_mul 2 1048576 379,
    Nat.pow_add 2 (1048576 * 600) 993297, Nat.pow_mul 2 1048576 600]
  decide +kernel

end CollatzBig.CircuitCert
