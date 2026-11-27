import Collatz.Bernoulli

/-!
# The law of large numbers for the parities of the 2-adic 3x+1 map

Under `bernoulli` the coordinates are independent fair coins
(`iIndepFun_iff_map_fun_eq_infinitePi_map₀`), so the strong law of large numbers applies.
Transporting it along `paritySeq` gives, for Haar-almost every `x ∈ ℤ₂`:

* `odd_fraction_ae`: the fraction of odd points among `x, T x, …, T^(n-1) x` tends to `1/2`;
* `multiplier_rate_ae`: the multiplier `3^(s_n) / 2^n` of `T^n` (where `s_n` is that number of
  odd points) satisfies `log (3^(s_n) / 2^n) / n → log 3 / 2 - log 2 = log (√3 / 2) < 0`.

This is the heuristic behind the Collatz conjecture: on average each step multiplies by
`√3 / 2 < 1`.
-/

namespace Collatz.TwoAdic

open MeasureTheory ProbabilityTheory Filter Finset Topology

lemma bernoulli_map_eval (i : ℕ) : bernoulli.map (fun ω => ω i) = coin := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton b)]
  have : (fun ω : ℕ → Bool => ω i) ⁻¹' {b} = Set.pi ({i} : Finset ℕ) (fun _ => {b}) := by
    ext ω; simp
  rw [this, bernoulli, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp

lemma iIndep_coords : iIndepFun (fun i (ω : ℕ → Bool) => ω i) bernoulli := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ (X := fun i (ω : ℕ → Bool) => ω i)
    (by exact measurable_id.aemeasurable)]
  simp_rw [bernoulli_map_eval]
  have h1 : (fun (ω : ℕ → Bool) (i : ℕ) => ω i) = id := rfl
  rw [h1, Measure.map_id]
  rfl

/-- A bit as a real number. -/
noncomputable def bitR (b : Bool) : ℝ := if b then 1 else 0

lemma measurable_bitR : Measurable bitR := measurable_of_countable _

/-- The `i`-th coin as a real random variable. -/
noncomputable def Y (i : ℕ) (ω : ℕ → Bool) : ℝ := bitR (ω i)

lemma measurable_Y (i : ℕ) : Measurable (Y i) := measurable_bitR.comp (measurable_pi_apply i)

lemma Y_indep : Pairwise (Function.onFun (fun f g => IndepFun f g bernoulli) Y) := fun _ _ hij =>
  (iIndep_coords.comp (fun _ => bitR) (fun _ => measurable_bitR)).indepFun hij

lemma map_Y (i : ℕ) : bernoulli.map (Y i) = coin.map bitR := by
  rw [show Y i = bitR ∘ (fun ω => ω i) from rfl,
    ← Measure.map_map measurable_bitR (measurable_pi_apply i), bernoulli_map_eval]

lemma Y_ident (i : ℕ) : IdentDistrib (Y i) (Y 0) bernoulli bernoulli :=
  ⟨(measurable_Y i).aemeasurable, (measurable_Y 0).aemeasurable, by rw [map_Y, map_Y]⟩

lemma Y_integrable : Integrable (Y 0) bernoulli := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_Y 0).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  unfold Y bitR; split_ifs <;> simp

lemma Y_mean : bernoulli[Y 0] = 1 / 2 := by
  rw [show Y 0 = bitR ∘ (fun ω => ω 0) from rfl]
  change ∫ ω, bitR (ω 0) ∂bernoulli = 1 / 2
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
      measurable_bitR.aestronglyMeasurable, bernoulli_map_eval,
    integral_fintype (Integrable.of_finite)]
  simp [bitR, Measure.real, coin_singleton]

/-- **For Haar-almost every `x ∈ ℤ₂`, half of the points along the `T`-orbit are odd.** -/
theorem odd_fraction_ae :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (oddCount2 n x : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have h := strong_law_ae Y Y_integrable Y_indep Y_ident
  rw [Y_mean] at h
  have h2 := ae_of_ae_map paritySeq_measurePreserving.measurable.aemeasurable
    (by rw [paritySeq_measurePreserving.map_eq]; exact h)
  filter_upwards [h2] with x hx
  convert hx using 2 with n
  rw [smul_eq_mul, div_eq_inv_mul, oddCount2]
  push_cast
  congr 1
  refine sum_congr rfl (fun i _ => ?_)
  have := par_lt (T^[i] x)
  simp only [Y, bitR, paritySeq]
  rcases (by omega : par (T^[i] x) = 0 ∨ par (T^[i] x) = 1) with h | h <;> simp [h]

lemma log_rate_neg : Real.log 3 / 2 - Real.log 2 < 0 := by
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- **For Haar-almost every `x ∈ ℤ₂`, the multiplier `3^(s_n) / 2^n` of `T^n` decays like
`(√3 / 2)^n`.** -/
theorem multiplier_rate_ae :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log ((3 : ℝ) ^ oddCount2 n x / 2 ^ n) / n) atTop
      (𝓝 (Real.log 3 / 2 - Real.log 2)) := by
  filter_upwards [odd_fraction_ae] with x hx
  have hlim := (hx.mul_const (Real.log 3)).sub_const (Real.log 2)
  rw [show 1 / 2 * Real.log 3 - Real.log 2 = Real.log 3 / 2 - Real.log 2 by ring] at hlim
  refine hlim.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  show _ = Real.log ((3 : ℝ) ^ oddCount2 n x / 2 ^ n) / n
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  field_simp

end Collatz.TwoAdic
