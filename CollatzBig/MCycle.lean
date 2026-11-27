import CollatzBig.Circuit
import CollatzBig.MCycleCert
import Collatz.MCycle

/-!
# No nontrivial `m`-cycle with few blocks and few odd steps (Baker-free)

Simons and de Weger (2005) excluded `m`-cycles for `m ≤ 68` with Baker's theorem. Without it,
the verification `n < 7281311744` (`CollatzBig.Ext.descends_below`) and one Farey pair of
`log₂ 3` per range of `m` (`Collatz.reachesOne_of_mcycle`) give:

| odd blocks `m` | Farey pair `a/b < log₂ 3 < c/d` | no cycle with `k <` |
| --- | --- | --- |
| `≤ 13`  | `357638239/225644606 < 272500658/171928773` | `397573379` |
| `≤ 38`  | `85137581/53715833 < 187363077/118212940`   | `171928773` |
| `≤ 63`  | `85137581/53715833 < 102225496/64497107`    | `118212940` |
| `≤ 88`  | `85137581/53715833 < 17087915/10781274`     | `64497107`  |
| `≤ 469` | `16785921/10590737 < 301994/190537`         | `10781274`  |

(`k` = number of odd steps; every nontrivial cycle has `k ≥ 190537` by
`CollatzBig.Ext.odds_card_ge`, so for `m ≥ 470` this method gives nothing new.)
For `m = 1` (circuits) `CollatzBig.Circuit.no_circuit` reaches `6586818670`.
-/

namespace CollatzBig.MCycle

open Collatz

/-! Transport of the certificates from core's `^` to Mathlib's (see `CollatzBig.Circuit`). -/

lemma up_t {x y M : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) →
    (M + 1) * p 3 y ≤ M * p 2 x) : (M + 1) * 3 ^ y ≤ M * 2 ^ x := h _ fun _ _ => rfl

lemma low_t {x y : ℕ} (h : ∀ p : ℕ → ℕ → ℕ, (∀ a b, p a b = a ^ b) → p 2 x < p 3 y) :
    2 ^ x < 3 ^ y := h _ fun _ _ => rfl

lemma two_pow_lt_of_mul {x y R : ℕ} (hR : 1 ≤ R) (h : R * 2 ^ x ≤ (R - 1) * 3 ^ y) :
    2 ^ x < 3 ^ y := by
  by_contra hge
  have h2 := Nat.mul_le_mul_left R (not_lt.1 hge)
  have h3 : 0 < 3 ^ y := by positivity
  have h4 : (R - 1) * 3 ^ y < R * 3 ^ y := Nat.mul_lt_mul_of_pos_right (by omega) h3
  omega

/-- `2^357638239 < 3^225644606`, from `CollatzBig.CircuitCert.lowA`. -/
theorem low13 : 2 ^ (1048576 * 341 + 73823) < 3 ^ (1048576 * 215 + 200766) :=
  two_pow_lt_of_mul (by norm_num) (CollatzBig.Circuit.lowA_t CollatzBig.CircuitCert.lowA)

/-- At most `13` odd blocks: no nontrivial cycle with fewer than `397573379` odd steps. -/
theorem reachesOne_of_blocks_le_13 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 13) (hk : oddCount K n < 397573379) :
    ReachesOne n :=
  reachesOne_of_mcycle (N := 7281311744) (by norm_num) low13
    (up_t CollatzBig.MCycleCert.up13) (by decide +kernel) CollatzBig.Ext.reachesOne_below
    hn hK hper hm (by omega)

/-- At most `38` odd blocks: no nontrivial cycle with fewer than `171928773` odd steps. -/
theorem reachesOne_of_blocks_le_38 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 38) (hk : oddCount K n < 171928773) :
    ReachesOne n :=
  reachesOne_of_mcycle (N := 7281311744) (by norm_num) (low_t CollatzBig.MCycleCert.low38)
    (up_t CollatzBig.MCycleCert.up38) (by decide +kernel) CollatzBig.Ext.reachesOne_below
    hn hK hper hm (by omega)

/-- At most `63` odd blocks: no nontrivial cycle with fewer than `118212940` odd steps. -/
theorem reachesOne_of_blocks_le_63 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 63) (hk : oddCount K n < 118212940) :
    ReachesOne n :=
  reachesOne_of_mcycle (N := 7281311744) (by norm_num) (low_t CollatzBig.MCycleCert.low38)
    (up_t CollatzBig.MCycleCert.up63) (by decide +kernel) CollatzBig.Ext.reachesOne_below
    hn hK hper hm (by omega)

/-- At most `88` odd blocks: no nontrivial cycle with fewer than `64497107` odd steps. -/
theorem reachesOne_of_blocks_le_88 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 88) (hk : oddCount K n < 64497107) :
    ReachesOne n :=
  reachesOne_of_mcycle (N := 7281311744) (by norm_num) (low_t CollatzBig.MCycleCert.low38)
    (up_t CollatzBig.MCycleCert.up88) (by decide +kernel) CollatzBig.Ext.reachesOne_below
    hn hK hper hm (by omega)

/-- At most `469` odd blocks: no nontrivial cycle with fewer than `10781274` odd steps. -/
theorem reachesOne_of_blocks_le_469 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 469) (hk : oddCount K n < 10781274) :
    ReachesOne n :=
  reachesOne_of_mcycle (N := 7281311744) (by norm_num) (low_t CollatzBig.MCycleCert.low469)
    (up_t CollatzBig.MCycleCert.up469) (by decide +kernel) CollatzBig.Ext.reachesOne_below
    hn hK hper hm (by omega)

/-- **Bounded Simons–de Weger theorem** (Baker-free, `m ≤ 68`): a `T`-cycle with at most `68`
odd blocks and fewer than `64497107` odd steps consists of numbers reaching `1`. -/
theorem reachesOne_of_blocks_le_68 {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 68) (hk : oddCount K n < 64497107) :
    ReachesOne n :=
  reachesOne_of_blocks_le_88 hn hK hper (by omega) hk

end CollatzBig.MCycle
