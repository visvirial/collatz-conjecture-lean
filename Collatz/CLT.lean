import Collatz.LLN

/-!
# The central limit theorem for the parities of the 2-adic 3x+1 map

Under `bernoulli` the coordinates `Y i` are i.i.d. fair coins with mean `1/2` and variance
`1/4`, so Mathlib's central limit theorem `tendstoInDistribution_inv_sqrt_mul_sum_sub` applies.
Transporting it along the measure-preserving map `paritySeq : (ℤ₂, μ) → (ℕ → Bool, bernoulli)`
gives, under the Haar probability measure `μ`:

* `oddCount2_clt`: `(s_n - n / 2) / √n` converges in distribution to `𝒩(0, 1/4)`, where
  `s_n = oddCount2 n x` is the number of odd points among `x, T x, …, T^(n-1) x`;
* `multiplier_clt`: `(log (3^(s_n) / 2^n) - n log (√3 / 2)) / √n` converges in distribution to
  `𝒩(0, (log 3)² / 4)`.
-/

namespace Collatz.TwoAdic

open MeasureTheory ProbabilityTheory Filter Finset Topology

lemma iIndepFun_Y : iIndepFun Y bernoulli :=
  iIndep_coords.comp (fun _ => bitR) (fun _ => measurable_bitR)

lemma Y_sq (ω : ℕ → Bool) : Y 0 ω ^ 2 = Y 0 ω := by
  unfold Y bitR; split_ifs <;> simp

lemma Y_memLp : MemLp (Y 0) 2 bernoulli := by
  refine MemLp.of_bound (measurable_Y 0).aestronglyMeasurable 1 (ae_of_all _ (fun ω => ?_))
  unfold Y bitR; split_ifs <;> simp

lemma Y_variance : Var[Y 0; bernoulli] = 1 / 4 := by
  rw [variance_eq_sub Y_memLp, Y_mean]
  have : (Y 0 ^ 2 : (ℕ → Bool) → ℝ) = Y 0 := funext fun ω => by simp [Y_sq]
  rw [this, Y_mean]; norm_num

lemma sum_Y_paritySeq (n : ℕ) (x : ℤ_[2]) :
    ∑ i ∈ range n, Y i (paritySeq x) = (oddCount2 n x : ℝ) := by
  rw [oddCount2]
  push_cast
  refine sum_congr rfl (fun i _ => ?_)
  have := par_lt (T^[i] x)
  simp only [Y, bitR, paritySeq]
  rcases (by omega : par (T^[i] x) = 0 ∨ par (T^[i] x) = 1) with h | h <;> simp [h]

/-- **Central limit theorem for the parities of the 2-adic `3x+1` map.** Under the Haar
probability measure `μ` on `ℤ₂`, the normalized number of odd points
`(s_n - n / 2) / √n` along the orbit `x, T x, …, T^(n-1) x` converges in distribution to a
Gaussian with mean `0` and variance `1/4`. -/
theorem oddCount2_clt {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (1 / 4)) P') :
    TendstoInDistribution (fun (n : ℕ) (x : ℤ_[2]) => ((oddCount2 n x : ℝ) - n / 2) / √n)
      atTop Z (fun _ => μ) P' := by
  have hZ' : HasLaw Z (gaussianReal 0 Var[Y 0; bernoulli].toNNReal) P' := by
    convert hZ
    rw [Y_variance]
    ext; simp
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' Y_memLp iIndepFun_Y Y_ident
  rw [Y_mean] at h
  let f : ℕ → (ℕ → Bool) → ℝ :=
    fun n ω => (√n)⁻¹ * (∑ k ∈ range n, Y k ω - n * (1 / 2))
  have hfm : ∀ n, Measurable (f n) := fun n => by
    have : Measurable fun ω => ∑ k ∈ range n, Y k ω :=
      Finset.measurable_sum _ fun k _ => measurable_Y k
    exact measurable_const.mul (this.sub measurable_const)
  have heq : ∀ n, (fun x : ℤ_[2] => ((oddCount2 n x : ℝ) - n / 2) / √n) = f n ∘ paritySeq := by
    intro n; funext x
    simp only [f, Function.comp, sum_Y_paritySeq]
    ring
  have hmap : ∀ n, μ.map (fun x : ℤ_[2] => ((oddCount2 n x : ℝ) - n / 2) / √n) =
      bernoulli.map (f n) := by
    intro n
    rw [heq, ← Measure.map_map (hfm n) paritySeq_measurePreserving.measurable,
      paritySeq_measurePreserving.map_eq]
  refine ⟨fun n => ?_, h.aemeasurable_limit, ?_⟩
  · rw [heq]; exact ((hfm n).comp paritySeq_measurePreserving.measurable).aemeasurable
  · exact h.tendsto.congr (fun n => Subtype.ext (hmap n).symm)

lemma log_sqrt3_div2 : Real.log (√3 / 2) = Real.log 3 / 2 - Real.log 2 := by
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]

/-- **Central limit theorem for the multiplier of `T^n`.** Under the Haar probability measure
`μ` on `ℤ₂`, `(log (3^(s_n) / 2^n) - n log (√3 / 2)) / √n` converges in distribution to a
Gaussian with mean `0` and variance `(log 3)² / 4`. -/
theorem multiplier_clt {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {W : Ω' → ℝ}
    (hW : HasLaw W (gaussianReal 0 (Real.log 3 ^ 2 / 4).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) (x : ℤ_[2]) =>
        (Real.log ((3 : ℝ) ^ oddCount2 n x / 2 ^ n) - n * Real.log (√3 / 2)) / √n)
      atTop W (fun _ => μ) P' := by
  have hl : Real.log 3 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3); exact this.ne'
  have hZ : HasLaw (fun ω => W ω / Real.log 3) (gaussianReal 0 (1 / 4)) P' := by
    have hnn : (0 : ℝ) ≤ Real.log 3 ^ 2 / 4 := div_nonneg (sq_nonneg _) (by norm_num)
    have hv : (Real.log 3 ^ 2 / 4).toNNReal / NNReal.mk (Real.log 3 ^ 2) (sq_nonneg _) = 1 / 4 := by
      apply NNReal.eq
      rw [NNReal.coe_div, Real.coe_toNNReal _ hnn, NNReal.coe_mk]
      push_cast
      field_simp
    have := gaussianReal_div_const hW (Real.log 3)
    rwa [zero_div, hv] at this
  have h := (oddCount2_clt hZ).continuous_comp (g := fun t => Real.log 3 * t)
    (continuous_const.mul continuous_id)
  convert h using 1
  · funext n x
    simp only [Function.comp]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      log_sqrt3_div2]
    ring
  · funext ω
    simp only [Function.comp]
    field_simp

end Collatz.TwoAdic
