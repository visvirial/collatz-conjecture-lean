import Collatz.StoppingDist

/-!
# Exponential decay of the stopping time tail (Lagarias' Theorem D)

Let `θ = log 2 / log 3 ≈ 0.6309`. A residue mod `2^k` whose coefficient has not dropped below
`1` after `k` steps has at least `θ k` odd steps, so weighting residues by
`θ^s (1-θ)^(k-s)` (total weight `1` by `sum_weight_real`) gives

  `#{r < 2^k | r ∉ goodSet k} ≤ #badSet k ≤ exp (k H(θ))`,

with `H` the binary entropy; `H(θ) / log 2 ≈ 0.94996`. With `density_stopsBy`, the integers
whose stopping time exceeds `k` have density at most `exp (-(log 2 - H(θ)) k) ≈ 2^(-0.05 k)`.
-/

namespace Collatz

open Finset Real

/-- `θ = log 2 / log 3`. -/
noncomputable def theta : ℝ := Real.log 2 / Real.log 3

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma log_three_pos' : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma theta_pos : 0 < theta := div_pos log_two_pos' log_three_pos'

lemma theta_lt_one : theta < 1 := by
  rw [theta, div_lt_one log_three_pos']
  exact Real.log_lt_log (by norm_num) (by norm_num)

lemma half_lt_theta : 1 / 2 < theta := by
  rw [theta, lt_div_iff₀ log_three_pos']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

theorem sum_weight_real (a b : ℝ) : ∀ k : ℕ,
    ∑ r ∈ range (2 ^ k), a ^ oddCount k r * b ^ (k - oddCount k r) = (a + b) ^ k
  | 0 => by simp [oddCount]
  | k + 1 => by
    rw [sum_pair (fun s => a ^ s * b ^ (k + 1 - s)) k, pow_succ, ← sum_weight_real a b k, sum_mul]
    refine sum_congr rfl (fun r _ => ?_)
    have hs := oddCount_le k r
    obtain ⟨t, ht⟩ : ∃ t, k - oddCount k r = t := ⟨_, rfl⟩
    rw [ht, show k + 1 - oddCount k r = t + 1 by omega,
      show k + 1 - (oddCount k r + 1) = t by omega]
    ring

lemma binEntropy_theta : binEntropy theta =
    -(theta * Real.log theta) - (1 - theta) * Real.log (1 - theta) := by
  rw [binEntropy, Real.log_inv, Real.log_inv]; ring

/-- On a bad residue the weight `θ^s (1-θ)^(k-s)` is at least `exp (-k H(θ))`. -/
lemma weight_lower {k s : ℕ} (hs : s ≤ k) (h : 2 ^ k ≤ 3 ^ s) :
    Real.exp (-(k * binEntropy theta)) ≤ theta ^ s * (1 - theta) ^ (k - s) := by
  have hθ := theta_pos
  have hθ1 : 0 < 1 - theta := by linarith [theta_lt_one]
  have hw : 0 < theta ^ s * (1 - theta) ^ (k - s) := by positivity
  rw [← Real.exp_log hw, Real.exp_le_exp, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Nat.cast_sub hs, binEntropy_theta]
  -- s ≥ k θ
  have hks : (k : ℝ) * theta ≤ s := by
    have h' : ((2 : ℝ) ^ k) ≤ 3 ^ s := by exact_mod_cast h
    have hl := Real.log_le_log (by positivity) h'
    rw [Real.log_pow, Real.log_pow] at hl
    rw [theta, mul_div_assoc', div_le_iff₀ log_three_pos']
    linarith
  have hlog : Real.log (1 - theta) < Real.log theta :=
    Real.log_lt_log hθ1 (by linarith [half_lt_theta])
  nlinarith [mul_nonneg (sub_nonneg.2 hks) (sub_nonneg.2 hlog.le)]

/-- **Lagarias' Theorem D**: `#badSet k ≤ exp (k H(θ))`. -/
theorem badSet_card_le (k : ℕ) : ((badSet k).card : ℝ) ≤ Real.exp (k * binEntropy theta) := by
  have hθ := theta_pos
  have hθ1 : 0 < 1 - theta := by linarith [theta_lt_one]
  have htotal := sum_weight_real theta (1 - theta) k
  rw [show theta + (1 - theta) = 1 by ring, one_pow] at htotal
  have h1 : ((badSet k).card : ℝ) * Real.exp (-(k * binEntropy theta)) ≤ 1 := by
    calc ((badSet k).card : ℝ) * Real.exp (-(k * binEntropy theta))
        = ∑ r ∈ badSet k, Real.exp (-(k * binEntropy theta)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ badSet k, theta ^ oddCount k r * (1 - theta) ^ (k - oddCount k r) := by
          refine sum_le_sum (fun r hr => ?_)
          simp only [badSet, mem_filter] at hr
          exact weight_lower (oddCount_le k r) hr.2
      _ ≤ ∑ r ∈ range (2 ^ k), theta ^ oddCount k r * (1 - theta) ^ (k - oddCount k r) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = 1 := htotal
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)] at h1
  exact h1

/-- The residues that have not stopped by step `k` lie in `badSet k`. -/
lemma sdiff_goodSet_subset (k : ℕ) : range (2 ^ k) \ goodSet k ⊆ badSet k := by
  intro r hr
  rw [mem_sdiff, mem_range] at hr
  have halive := (not_mem_goodSet hr.1).1 hr.2
  simp only [badSet, mem_filter, mem_range]
  refine ⟨hr.1, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; simp [oddCount]
  · exact halive k (by simp; omega)

/-- The number of residues mod `2^k` with stopping time `> k` is at most `exp (k H(θ))`. -/
theorem card_not_good_le (k : ℕ) :
    ((2 ^ k - (goodSet k).card : ℕ) : ℝ) ≤ Real.exp (k * binEntropy theta) := by
  have hsub : goodSet k ⊆ range (2 ^ k) := filter_subset _ _
  rw [← card_range (2 ^ k), ← card_sdiff_of_subset hsub]
  exact le_trans (by exact_mod_cast card_le_card (sdiff_goodSet_subset k)) (badSet_card_le k)

theorem binEntropy_theta_lt : binEntropy theta < Real.log 2 :=
  binEntropy_lt_log_two.2 (by have := half_lt_theta; intro h; rw [h] at this; norm_num at this)

/-- The density of integers with stopping time `> k` decays exponentially:
`1 - #goodSet k / 2^k ≤ exp (-(log 2 - H(θ)) k)`, with `log 2 - H(θ) > 0`. -/
theorem density_tail_le (k : ℕ) :
    1 - ((goodSet k).card : ℝ) / 2 ^ k ≤ Real.exp (-((Real.log 2 - binEntropy theta) * k)) := by
  have hsub : (goodSet k).card ≤ 2 ^ k := by
    have := card_le_card (filter_subset (fun r => ∃ j ∈ Icc 1 k, 3 ^ oddCount j r < 2 ^ j)
      (range (2 ^ k)))
    rwa [card_range] at this
  have h := card_not_good_le k
  rw [Nat.cast_sub hsub] at h
  push_cast at h
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have e : Real.exp (-((Real.log 2 - binEntropy theta) * k)) =
      Real.exp (k * binEntropy theta) / 2 ^ k := by
    rw [show (2 : ℝ) ^ k = Real.exp (k * Real.log 2) by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]]
    rw [← Real.exp_sub]; ring_nf
  rw [e, one_sub_div h2.ne', div_le_div_iff_of_pos_right h2]
  exact h

end Collatz
