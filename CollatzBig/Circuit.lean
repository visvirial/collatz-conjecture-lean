import CollatzBig.Ext
import CollatzBig.CircuitCert
import Collatz.Circuit

/-!
# No nontrivial circuit with fewer than 6586818670 odd steps

Steiner (1977) showed with Baker's theorem that `1 → 2 → 1` is the only circuit (a `T`-cycle
with one run of odd steps and one run of even steps). Without Baker, the verification
`n < 7281311744` (`CollatzBig.Ext.descends_below`) and one Farey pair of `log₂ 3` exclude every
other circuit with fewer than `6586818670` odd steps.

The pair is formed by the consecutive convergents

  `9809721694 / 6189245291 < log₂ 3 < 630138897 / 397573379`,

so `b + d = 6586818670` is the denominator of the next convergent `10439860591 / 6586818670`.
The lower bound would need a numeral of `9.8 · 10^9` bits, above the kernel's limit, so it is
assembled (`two_pow_lt_of_anchors`) from `lowA` (`357638239 / 225644606`) and fifteen copies
of `upR`, since `9809721694 = 357638239 + 15 · 630138897` and
`6189245291 = 225644606 + 15 · 397573379`. The upper fraction leaves only the candidate
`(K, k) = (630138897, 397573379)`, for which `n` would be `≈ 9447912335.13`; `notDvd` excludes it.
-/

namespace CollatzBig.Circuit

open Collatz

/-! The certificates are stated for any `p` equal to core's `^`. These transport lemmas
instantiate `p` with Mathlib's `^` (`Monoid.npow`); the defeq checks happen under the binder `p`
or with variable exponents, so no power is evaluated. -/

lemma lowA_t {x y : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) →
    594045519 * p 2 x ≤ (594045519 - 1) * p 3 y) :
    594045519 * 2 ^ x ≤ (594045519 - 1) * 3 ^ y := h _ fun _ _ => rfl

lemma upR_t {x y : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) →
    9447912334 * p 2 x ≤ (9447912334 + 1) * p 3 y) :
    9447912334 * 2 ^ x ≤ (9447912334 + 1) * 3 ^ y := h _ fun _ _ => rfl

lemma upN_t {x y : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) →
    (2 * 7281311744 + 1) * p 3 y ≤ 2 * 7281311744 * p 2 x) :
    (2 * 7281311744 + 1) * 3 ^ y ≤ 2 * 7281311744 * 2 ^ x := h _ fun _ _ => rfl

lemma notDvd_t {x y : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) →
    (p 3 y - p 2 y) % (p 2 x - p 3 y) ≠ 0) :
    (3 ^ y - 2 ^ y) % (2 ^ x - 3 ^ y) ≠ 0 := h _ fun _ _ => rfl

/-- `2^9809721694 < 3^6189245291`, i.e. `9809721694 / 6189245291 < log₂ 3`. -/
theorem lower :
    2 ^ ((1048576 * 341 + 73823) + 15 * (1048576 * 600 + 993297))
      < 3 ^ ((1048576 * 215 + 200766) + 15 * (1048576 * 379 + 163075)) :=
  two_pow_lt_of_anchors (lowA_t CollatzBig.CircuitCert.lowA) (upR_t CollatzBig.CircuitCert.upR)
    (by norm_num)

/-- **Bounded Steiner theorem.** Every circuit with fewer than `6586818670` odd steps is the
trivial circuit `1 → 2 → 1`. -/
theorem no_circuit {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 6586818670) :
    n = 1 ∧ k = 1 ∧ l = 1 :=
  no_circuit_of_farey' (N := 7281311744) (by norm_num) lower (by norm_num)
    (upN_t CollatzBig.CircuitCert.upN) (notDvd_t CollatzBig.CircuitCert.notDvd)
    CollatzBig.Ext.reachesOne_below hc
    (by omega)

/-- A circuit with fewer than `6586818670` odd steps reaches `1`. -/
theorem reachesOne_of_circuit {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 6586818670) :
    ReachesOne n := by
  rw [(no_circuit hc hk).1]
  exact reachesOne_one

end CollatzBig.Circuit
