import Collatz.LLN

/-!
# Equidistribution of 2-adic 3x+1 orbits

The second half of Lagarias' Theorem K (due to Matthews–Watts 1984): for Haar-almost every `x ∈ ℤ₂`, the `T`-orbit of `x`
is equidistributed modulo `2^k` for every `k`. That is, for every ball `B = closedBall a (2^-k)`
the fraction of `i < n` with `T^i x ∈ B` tends to `2^-k` (`orbit_equidistributed`).

Mathlib has no pointwise ergodic theorem, so we use a block form of the strong law.
Via `Q`, `T^i x ∈ B` iff the parities `paritySeq x (i), …, paritySeq x (i + k - 1)` equal the first
`k` binary digits of `Q a` (`iterate_mem_ball_iff`). On the Bernoulli space, the indicators `Z i`
of such windows at positions `j (k + 1) + c` (for fixed `c`) depend on disjoint blocks of
coordinates, hence are pairwise independent, and they are identically distributed with mean
`2^-k`. The strong law applies to each of the `k + 1` residue subsequences, and averaging them
(`tendsto_avg_of_blocks`) gives the full Cesàro average. We transport along `paritySeq` and
quantify over the countably many balls `closedBall d (2^-k)` with `d ∈ ℕ`.
-/

namespace Collatz.TwoAdic

open PadicInt MeasureTheory ProbabilityTheory Metric Filter Finset Topology

/-! ## Balls in terms of parities -/

lemma mem_ball_iff_bits (y z : ℤ_[2]) (k : ℕ) :
    y ∈ closedBall z (rad k) ↔ ∀ j < k, bits y j = bits z j := by
  have h := Set.ext_iff.1 (ofBits_preimage_ball z k) (bits y)
  simpa [ofBits_bits] using h

lemma paritySeq_iterate (x : ℤ_[2]) (i : ℕ) :
    paritySeq (T^[i] x) = fun j => paritySeq x (j + i) := by
  funext j
  simp only [paritySeq, Function.iterate_add_apply]

/-- `T^i x` lies in the ball of radius `2^-k` around `a` iff the parities at positions
`i, …, i + k - 1` of the orbit of `x` are the first `k` binary digits of `Q a`. -/
theorem iterate_mem_ball_iff (x a : ℤ_[2]) (k i : ℕ) :
    T^[i] x ∈ closedBall a (rad k) ↔ ∀ j < k, paritySeq x (j + i) = bits (Q a) j := by
  rw [mem_ball_iff, ← pow_dvd_Q_sub_iff, ← mem_ball_iff, mem_ball_iff_bits,
    ← paritySeq_eq (T^[i] x)]
  simp only [paritySeq_iterate]

/-! ## Windows on the Bernoulli space -/

/-- The shift by `i` on coin sequences. -/
def bshift (i : ℕ) (ω : ℕ → Bool) : ℕ → Bool := fun j => ω (j + i)

lemma measurable_bshift (i : ℕ) : Measurable (bshift i) :=
  measurable_pi_iff.2 (fun j => measurable_pi_apply (j + i))

lemma bshift_paritySeq (i : ℕ) (x : ℤ_[2]) : bshift i (paritySeq x) = paritySeq (T^[i] x) :=
  (paritySeq_iterate x i).symm

theorem bshift_measurePreserving (i : ℕ) : MeasurePreserving (bshift i) bernoulli bernoulli := by
  refine ⟨measurable_bshift i, ?_⟩
  have hp := paritySeq_measurePreserving
  have hT := T_measurePreserving.iterate i
  rw [← hp.map_eq, Measure.map_map (measurable_bshift i) hp.measurable]
  have : bshift i ∘ paritySeq = paritySeq ∘ T^[i] := funext fun x => bshift_paritySeq i x
  rw [this, ← Measure.map_map hp.measurable hT.measurable, hT.map_eq]

/-- The sequences starting with the word `w` of length `k`. -/
def wcyl (w : ℕ → Bool) (k : ℕ) : Set (ℕ → Bool) :=
  Set.pi (Finset.range k : Set ℕ) (fun j => {w j})

lemma measurableSet_wcyl (w : ℕ → Bool) (k : ℕ) : MeasurableSet (wcyl w k) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_singleton _)

/-- The sequences showing the word `w` of length `k` at position `i`. -/
def wwin (w : ℕ → Bool) (k i : ℕ) : Set (ℕ → Bool) := bshift i ⁻¹' wcyl w k

lemma mem_wwin {w : ℕ → Bool} {k i : ℕ} {ω : ℕ → Bool} :
    ω ∈ wwin w k i ↔ ∀ j < k, ω (j + i) = w j := by
  simp [wwin, wcyl, bshift]

lemma measurableSet_wwin (w : ℕ → Bool) (k i : ℕ) : MeasurableSet (wwin w k i) :=
  measurable_bshift i (measurableSet_wcyl w k)

lemma measure_wwin (w : ℕ → Bool) (k i : ℕ) : bernoulli (wwin w k i) = ((2 : ENNReal) ^ k)⁻¹ := by
  show bernoulli (bshift i ⁻¹' wcyl w k) = _
  rw [(bshift_measurePreserving i).measure_preimage (measurableSet_wcyl w k).nullMeasurableSet]
  exact bernoulli_box w k

/-- The indicator of the window `wwin w k i`. -/
noncomputable def wZ (w : ℕ → Bool) (k i : ℕ) (ω : ℕ → Bool) : ℝ := (wwin w k i).indicator 1 ω

lemma measurable_wZ (w : ℕ → Bool) (k i : ℕ) : Measurable (wZ w k i) :=
  measurable_one.indicator (measurableSet_wwin w k i)

lemma wZ_nonneg (w : ℕ → Bool) (k i : ℕ) (ω : ℕ → Bool) : 0 ≤ wZ w k i ω := by
  classical
  unfold wZ; rw [Set.indicator_apply]; split_ifs <;> norm_num

lemma wZ_le_one (w : ℕ → Bool) (k i : ℕ) (ω : ℕ → Bool) : wZ w k i ω ≤ 1 := by
  classical
  unfold wZ; rw [Set.indicator_apply]; split_ifs <;> norm_num

lemma integrable_wZ (w : ℕ → Bool) (k i : ℕ) : Integrable (wZ w k i) bernoulli :=
  (integrable_const (1 : ℝ)).mono' (measurable_wZ w k i).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wZ_nonneg w k i ω)]; exact wZ_le_one w k i ω)

lemma integral_wZ (w : ℕ → Bool) (k i : ℕ) :
    ∫ ω, wZ w k i ω ∂bernoulli = ((2 : ℝ) ^ k)⁻¹ := by
  show ∫ ω, (wwin w k i).indicator 1 ω ∂bernoulli = _
  rw [integral_indicator_one (measurableSet_wwin w k i)]
  simp only [Measure.real, measure_wwin, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

lemma wZ_comp (w : ℕ → Bool) (k i : ℕ) : wZ w k i = (wcyl w k).indicator 1 ∘ bshift i := by
  funext ω
  rfl

lemma identDistrib_wZ (w : ℕ → Bool) (k i : ℕ) :
    IdentDistrib (wZ w k i) (wZ w k 0) bernoulli bernoulli := by
  have hg : Measurable ((wcyl w k).indicator (1 : (ℕ → Bool) → ℝ)) :=
    measurable_one.indicator (measurableSet_wcyl w k)
  have hmap : ∀ i, bernoulli.map (wZ w k i) = bernoulli.map ((wcyl w k).indicator 1) := by
    intro i
    rw [wZ_comp, ← Measure.map_map hg (measurable_bshift i), (bshift_measurePreserving i).map_eq]
  exact ⟨(measurable_wZ w k i).aemeasurable, (measurable_wZ w k 0).aemeasurable,
    by rw [hmap, hmap]⟩

/-! ## Independence of disjoint windows -/

/-- `wZ w k i` as a function of the coordinates in `[i, i + k)`. -/
noncomputable def blockFun (w : ℕ → Bool) (k i : ℕ) (v : Finset.Ico i (i + k) → Bool) : ℝ :=
  Set.indicator {v : Finset.Ico i (i + k) → Bool | ∀ j (hj : j < k),
    v ⟨j + i, Finset.mem_Ico.2 ⟨by omega, by omega⟩⟩ = w j} 1 v

lemma wZ_eq_block (w : ℕ → Bool) (k i : ℕ) :
    wZ w k i = blockFun w k i ∘ (fun ω (l : Finset.Ico i (i + k)) => ω l) := by
  funext ω
  simp only [wZ, blockFun, Function.comp]
  by_cases h : ∀ j < k, ω (j + i) = w j
  · rw [Set.indicator_of_mem (mem_wwin.2 h), Set.indicator_of_mem (by exact fun j hj => h j hj)]
    rfl
  · rw [Set.indicator_of_notMem (mt mem_wwin.1 h),
      Set.indicator_of_notMem (by exact fun h' => h fun j hj => h' j hj)]

lemma indepFun_wZ (w : ℕ → Bool) (k : ℕ) {i i' : ℕ}
    (h : Disjoint (Finset.Ico i (i + k)) (Finset.Ico i' (i' + k))) :
    IndepFun (wZ w k i) (wZ w k i') bernoulli := by
  rw [wZ_eq_block w k i, wZ_eq_block w k i']
  exact (iIndep_coords.indepFun_finset _ _ h (fun l => measurable_pi_apply l)).comp
    (measurable_of_countable _) (measurable_of_countable _)

lemma disjoint_blocks (k c : ℕ) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (Finset.Ico (j * (k + 1) + c) (j * (k + 1) + c + k))
      (Finset.Ico (j' * (k + 1) + c) (j' * (k + 1) + c + k)) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  rw [Finset.mem_Ico] at h1 h2
  rcases Nat.lt_or_gt_of_ne h with hj | hj
  · have := Nat.mul_le_mul_right (k + 1) (show j + 1 ≤ j' from hj)
    rw [add_mul, one_mul] at this
    omega
  · have := Nat.mul_le_mul_right (k + 1) (show j' + 1 ≤ j from hj)
    rw [add_mul, one_mul] at this
    omega

/-- The strong law along the positions `j (k + 1) + c`. -/
lemma slln_offset (w : ℕ → Bool) (k c : ℕ) :
    ∀ᵐ ω ∂bernoulli, Tendsto (fun J : ℕ => (J : ℝ)⁻¹ • ∑ j ∈ range J, wZ w k (j * (k + 1) + c) ω)
      atTop (𝓝 ((2 : ℝ) ^ k)⁻¹) := by
  have h := strong_law_ae (fun j => wZ w k (j * (k + 1) + c)) (integrable_wZ w k _)
    (fun j j' hjj' => indepFun_wZ w k (disjoint_blocks k c hjj'))
    (fun j => (identDistrib_wZ w k _).trans (identDistrib_wZ w k _).symm)
  simp only [integral_wZ] at h
  exact h

/-! ## Averaging the residue subsequences -/

lemma sum_range_mul_eq (z : ℕ → ℝ) (m : ℕ) : ∀ J : ℕ,
    ∑ i ∈ range (J * m), z i = ∑ c ∈ range m, ∑ j ∈ range J, z (j * m + c)
  | 0 => by simp
  | J + 1 => by
    rw [add_mul, one_mul, sum_range_add, sum_range_mul_eq z m J]
    simp only [sum_range_succ, sum_add_distrib]

/-- If each residue subsequence `z (j m + c)` has Cesàro limit `p`, so does `z`. -/
theorem tendsto_avg_of_blocks {z : ℕ → ℝ} (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) {m : ℕ}
    (hm : 0 < m) {p : ℝ}
    (h : ∀ c < m, Tendsto (fun J : ℕ => (J : ℝ)⁻¹ * ∑ j ∈ range J, z (j * m + c)) atTop (𝓝 p)) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, z i) / n) atTop (𝓝 p) := by
  -- along multiples of `m`
  have hsub : Tendsto (fun J : ℕ => (∑ i ∈ range (J * m), z i) / ((J * m : ℕ) : ℝ))
      atTop (𝓝 p) := by
    have h2 : Tendsto (fun J : ℕ => (m : ℝ)⁻¹ *
        ∑ c ∈ range m, (J : ℝ)⁻¹ * ∑ j ∈ range J, z (j * m + c)) atTop
        (𝓝 ((m : ℝ)⁻¹ * ∑ c ∈ range m, p)) :=
      (tendsto_finsetSum _ (fun c hc => h c (mem_range.1 hc))).const_mul _
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hp : (m : ℝ)⁻¹ * ∑ c ∈ range m, p = p := by
      rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]
    rw [hp] at h2
    refine h2.congr (fun J => ?_)
    rw [sum_range_mul_eq z m J, ← Finset.mul_sum]
    push_cast
    ring
  -- the remainders
  have hr : Tendsto (fun n : ℕ => ((n % m : ℕ) : ℝ) / n) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity)
      (fun n => by gcongr; exact_mod_cast (Nat.mod_lt n hm).le)
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
  have hR : Tendsto (fun n : ℕ => (∑ x ∈ range (n % m), z (n / m * m + x)) / n)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => div_nonneg (sum_nonneg fun x _ => hz0 _) (Nat.cast_nonneg n))
      (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    gcongr
    calc ∑ x ∈ range (n % m), z (n / m * m + x) ≤ ∑ x ∈ range (n % m), (1 : ℝ) :=
          sum_le_sum fun x _ => hz1 _
      _ = ((n % m : ℕ) : ℝ) := by simp
      _ ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  have hf2 : Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have := hr.const_sub 1
    rw [sub_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have e : ((n / m * m : ℕ) : ℝ) = n - ((n % m : ℕ) : ℝ) := by
      have := Nat.div_add_mod' n m
      rw [eq_sub_iff_add_eq]
      exact_mod_cast this
    show _ = ((n / m * m : ℕ) : ℝ) / n
    rw [e, sub_div, div_self hn']
  have hlim := ((hsub.comp (Nat.tendsto_div_const_atTop hm.ne')).mul hf2).add hR
  rw [mul_one, add_zero] at hlim
  refine hlim.congr (fun n => ?_)
  have e : ∑ i ∈ range n, z i =
      ∑ i ∈ range (n / m * m), z i + ∑ x ∈ range (n % m), z (n / m * m + x) := by
    rw [← sum_range_add, Nat.div_add_mod']
  simp only [Function.comp]
  rw [e, add_div]
  congr 1
  rcases Nat.eq_zero_or_pos (n / m * m) with h0 | h0
  · rw [h0]; simp
  · exact div_mul_div_cancel₀ (Nat.cast_ne_zero.2 h0.ne')

/-! ## Equidistribution -/

/-- For almost every coin sequence, the word `w` of length `k` appears with frequency `2^-k`. -/
theorem ae_window_freq (w : ℕ → Bool) (k : ℕ) :
    ∀ᵐ ω ∂bernoulli, Tendsto (fun n : ℕ => (∑ i ∈ range n, wZ w k i ω) / n) atTop
      (𝓝 ((2 : ℝ) ^ k)⁻¹) := by
  have h := ae_all_iff.2 (fun c => slln_offset w k c)
  filter_upwards [h] with ω hω
  exact tendsto_avg_of_blocks (fun i => wZ_nonneg w k i ω) (fun i => wZ_le_one w k i ω)
    (Nat.succ_pos k) (fun c _ => by simpa only [smul_eq_mul] using hω c)

lemma wZ_paritySeq_of_mem {x a : ℤ_[2]} {k i : ℕ} (h : T^[i] x ∈ closedBall a (rad k)) :
    wZ (bits (Q a)) k i (paritySeq x) = 1 :=
  Set.indicator_of_mem (mem_wwin.2 ((iterate_mem_ball_iff x a k i).1 h)) _

lemma wZ_paritySeq_of_not_mem {x a : ℤ_[2]} {k i : ℕ} (h : T^[i] x ∉ closedBall a (rad k)) :
    wZ (bits (Q a)) k i (paritySeq x) = 0 :=
  Set.indicator_of_notMem (fun h' => h ((iterate_mem_ball_iff x a k i).2 (mem_wwin.1 h'))) _

open Classical in
/-- **Lagarias' Theorem K (equidistribution)**: for Haar-almost every `x ∈ ℤ₂`, the `T`-orbit
of `x` is equidistributed modulo `2^k` for every `k`: it visits every ball of radius `2^-k`
with asymptotic frequency `2^-k`. -/
theorem orbit_equidistributed : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ a : ℤ_[2],
    Tendsto (fun n : ℕ =>
      ((((range n).filter (fun i => T^[i] x ∈ closedBall a (rad k))).card : ℕ) : ℝ) / n)
      atTop (𝓝 ((2 : ℝ) ^ k)⁻¹) := by
  have h : ∀ᵐ x ∂μ, ∀ k d : ℕ, Tendsto
      (fun n : ℕ => (∑ i ∈ range n, wZ (bits (Q (d : ℤ_[2]))) k i (paritySeq x)) / n)
      atTop (𝓝 ((2 : ℝ) ^ k)⁻¹) := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro d
    exact ae_of_ae_map paritySeq_measurePreserving.measurable.aemeasurable
      (by rw [paritySeq_measurePreserving.map_eq]; exact ae_window_freq (bits (Q (d : ℤ_[2]))) k)
  filter_upwards [h] with x hx k a
  have hb : closedBall a (rad k) = closedBall ((a.appr k : ℕ) : ℤ_[2]) (rad k) :=
    (IsUltrametricDist.closedBall_eq_of_mem (mem_ball_appr a k)).symm
  refine (hx k (a.appr k)).congr (fun n => ?_)
  rw [card_filter]
  push_cast
  congr 1
  refine sum_congr rfl (fun i _ => ?_)
  split_ifs with hi
  · rw [hb] at hi; exact wZ_paritySeq_of_mem hi
  · rw [hb] at hi; exact wZ_paritySeq_of_not_mem hi

/-- The same statement for residues: for Haar-almost every `x`, for every `k` and `d < 2^k`,
the fraction of `i < n` with `T^i x ≡ d (mod 2^k)` tends to `2^-k`. -/
theorem orbit_equidistributed_mod : ∀ᵐ x ∂μ, ∀ k d : ℕ, d < 2 ^ k →
    Tendsto (fun n : ℕ =>
      ((((range n).filter (fun i => (T^[i] x).appr k = d)).card : ℕ) : ℝ) / n)
      atTop (𝓝 ((2 : ℝ) ^ k)⁻¹) := by
  filter_upwards [orbit_equidistributed] with x hx k d hd
  refine (hx k (d : ℤ_[2])).congr (fun n => ?_)
  congr 3
  ext i
  simp only [mem_filter]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have h1 := (mem_ball_iff _ _ _).1 h
    have h2 := (mem_ball_iff _ _ _).1 (mem_ball_appr (T^[i] x) k)
    have := dvd_sub h1 h2
    rw [show T^[i] x - (d : ℤ_[2]) - (T^[i] x - (((T^[i] x).appr k : ℕ) : ℤ_[2])) =
      (((T^[i] x).appr k : ℕ) : ℤ_[2]) - d by ring] at this
    exact nat_eq_of_pow_dvd (appr_lt _ k) hd this
  · intro h
    have := mem_ball_appr (T^[i] x) k
    rwa [h] at this

end Collatz.TwoAdic
