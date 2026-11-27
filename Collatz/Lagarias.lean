import Collatz.Terras

/-!
# The 3x+1 conjugacy map (Lagarias), at every finite level

Let `Q_k n = ∑_{i < k} (T^i n mod 2) 2^i` be the first `k` parities of the `T`-orbit of `n`,
read as a binary number. Lagarias (1985) showed that the 2-adic limit `Q_∞ : ℤ₂ → ℤ₂` is an
isometry and a bijection that conjugates `T` to the shift `x ↦ ⌊x / 2⌋`. Its content at
level `k` is:

* `parityVec_eq_iff`: `Q_k n = Q_k n' ↔ n ≡ n' (mod 2^k)` (so `Q_∞` is an isometry);
* `parityVec_bijective`: `Q_k` permutes the residues mod `2^k` (so `Q_∞` is onto);
* `parityVec_compat`: `Q_(k+1) n ≡ Q_k n (mod 2^k)` (the levels are compatible);
* `parityVec_kstepT`: `Q_k (T n) = Q_(k+1) n / 2` (conjugacy to the shift).
-/

namespace Collatz

open Finset

/-- The first `k` parities of the `T`-orbit of `n`, as a binary number. -/
def parityVec (k n : ℕ) : ℕ := ∑ i ∈ range k, kstepT^[i] n % 2 * 2 ^ i

lemma parityVec_succ (k n : ℕ) :
    parityVec (k + 1) n = parityVec k n + kstepT^[k] n % 2 * 2 ^ k := by
  rw [parityVec, parityVec, sum_range_succ]

lemma parityVec_lt (n : ℕ) : ∀ k, parityVec k n < 2 ^ k
  | 0 => by simp [parityVec]
  | k + 1 => by
    rw [parityVec_succ, pow_succ]
    have := parityVec_lt n k
    rcases Nat.mod_two_eq_zero_or_one (kstepT^[k] n) with h | h <;> rw [h] <;> omega

/-- `Q_(k+1) n = (n mod 2) + 2 Q_k (T n)`. -/
lemma parityVec_shift (k n : ℕ) : parityVec (k + 1) n = n % 2 + 2 * parityVec k (kstepT n) := by
  simp only [parityVec]
  rw [sum_range_succ', Finset.mul_sum, add_comm]
  simp only [Function.iterate_zero, id, pow_zero, mul_one]
  congr 1
  refine sum_congr rfl (fun i _ => ?_)
  rw [Function.iterate_succ_apply, pow_succ]
  ring

/-- Conjugacy: `Q_k (T n) = ⌊Q_(k+1) n / 2⌋`. -/
theorem parityVec_kstepT (k n : ℕ) : parityVec k (kstepT n) = parityVec (k + 1) n / 2 := by
  rw [parityVec_shift]
  have := Nat.mod_lt n two_pos
  omega

/-- Compatibility of the levels: `Q_(k+1) n mod 2^k = Q_k n`. -/
theorem parityVec_compat (k n : ℕ) : parityVec (k + 1) n % 2 ^ k = parityVec k n := by
  rw [parityVec_succ, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (parityVec_lt n k)]

lemma parityVec_affine (k m r : ℕ) : parityVec k (2 ^ k * m + r) = parityVec k r :=
  sum_congr rfl (fun i hi => by rw [parity_affine (mem_range.1 hi)])

lemma parityVec_mod (k n : ℕ) : parityVec k n = parityVec k (n % 2 ^ k) := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ k)]
  exact parityVec_affine k _ _

lemma parities_of_parityVec_eq : ∀ {k n n' : ℕ}, parityVec k n = parityVec k n' →
    ∀ i < k, kstepT^[i] n % 2 = kstepT^[i] n' % 2
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, n, n', h, i, hi => by
    rw [parityVec_succ, parityVec_succ] at h
    have h1 := parityVec_lt n k
    have h2 := parityVec_lt n' k
    have hb : kstepT^[k] n % 2 = kstepT^[k] n' % 2 ∧ parityVec k n = parityVec k n' := by
      rcases Nat.mod_two_eq_zero_or_one (kstepT^[k] n) with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one (kstepT^[k] n') with hb | hb <;>
      rw [ha, hb] at h ⊢ <;> omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact parities_of_parityVec_eq hb.2 i hi
    · exact hb.1

/-- `Q_k n = Q_k n'` iff `n ≡ n' (mod 2^k)`: the limit map is a 2-adic isometry. -/
theorem parityVec_eq_iff (k n n' : ℕ) : parityVec k n = parityVec k n' ↔ n % 2 ^ k = n' % 2 ^ k := by
  have hK : 0 < 2 ^ k := by positivity
  constructor
  · intro h
    rw [parityVec_mod k n, parityVec_mod k n'] at h
    exact parity_inj (Nat.mod_lt _ hK) (Nat.mod_lt _ hK) (parities_of_parityVec_eq h)
  · intro h
    rw [parityVec_mod k n, parityVec_mod k n', h]

/-- `Q_k` permutes the residues mod `2^k`. -/
theorem parityVec_bijective (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => (⟨parityVec k r, parityVec_lt r k⟩ : Fin (2 ^ k))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r r' h => Fin.ext ?_, rfl⟩
  have h' : parityVec k r = parityVec k r' := congrArg Fin.val h
  rw [parityVec_eq_iff, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] at h'
  exact h'

end Collatz
