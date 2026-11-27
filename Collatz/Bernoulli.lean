import Collatz.Ergodic

/-!
# The 2-adic 3x+1 map is a Bernoulli shift

Let `bernoulli` be the product of fair coins on `ℕ → Bool`. The binary digit map
`bits : ℤ₂ → (ℕ → Bool)` and its inverse `ofBits b = ∑' i, b i 2^i` are measure preserving
between `μ` and `bernoulli`, and `bits ∘ shift = (left shift) ∘ bits`.

Composing with `Q`, the parity sequence of the `T`-orbit,

  `paritySeq x = fun i => (T^i x is odd)`,

is a measure-preserving bijection `(ℤ₂, μ) → (ℕ → Bool, bernoulli)` with
`paritySeq (T x) = fun i => paritySeq x (i + 1)`: for a Haar-random 2-adic integer the
parities along its orbit are independent fair coin flips.
-/

namespace Collatz.TwoAdic

open PadicInt MeasureTheory Metric Set Finset

/-! ## Bits -/

/-- A bit as a 2-adic integer. -/
noncomputable def bv (b : Bool) : ℤ_[2] := if b then 1 else 0

lemma norm_bv_le (b : Bool) : ‖bv b‖ ≤ 1 := by cases b <;> simp [bv]

lemma par_bv (b : Bool) : par (bv b) = if b then 1 else 0 := by
  cases b
  · simpa [bv] using par_natCast 0
  · simpa [bv] using par_natCast 1

/-- The binary digits of a 2-adic integer. -/
noncomputable def bits (y : ℤ_[2]) : ℕ → Bool := fun i => decide (par (shift^[i] y) = 1)

lemma bv_bits_zero (y : ℤ_[2]) : bv (bits y 0) = (par y : ℤ_[2]) := by
  have := par_lt y
  simp only [bits, Function.iterate_zero, id, bv]
  rcases (by omega : par y = 0 ∨ par y = 1) with h | h <;> simp [h]

lemma bits_succ (y : ℤ_[2]) (i : ℕ) : bits y (i + 1) = bits (shift y) i := by
  unfold bits; rw [Function.iterate_succ_apply]

lemma bits_shift (y : ℤ_[2]) : bits (shift y) = fun i => bits y (i + 1) := by
  funext i; rw [bits_succ]

/-- `y = ∑_{i<k} (bit i) 2^i + 2^k shift^k y`. -/
lemma eq_bits_add (y : ℤ_[2]) : ∀ k : ℕ,
    y = ∑ i ∈ range k, bv (bits y i) * 2 ^ i + 2 ^ k * shift^[k] y
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ', Function.iterate_succ_apply]
    conv_lhs => rw [eq_par_add_shift y, eq_bits_add (shift y) k]
    simp only [bits_succ, pow_zero, mul_one, ← bv_bits_zero, pow_succ]
    have hs : ∑ x ∈ range k, bv (bits (shift y) x) * (2 ^ x * 2) =
        2 * ∑ i ∈ range k, bv (bits (shift y) i) * 2 ^ i := by
      rw [Finset.mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
    rw [hs]; ring

/-! ## From bits to 2-adic integers -/

lemma summable_ofBits (b : ℕ → Bool) : Summable (fun i => bv (b i) * (2 : ℤ_[2]) ^ i) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [norm_mul, norm_pow, show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, norm_p]
  calc ‖bv (b i)‖ * ((2 : ℕ) : ℝ)⁻¹ ^ i ≤ 1 * ((2 : ℕ) : ℝ)⁻¹ ^ i :=
        mul_le_mul_of_nonneg_right (norm_bv_le _) (by positivity)
    _ = (1 / 2) ^ i := by norm_num

/-- The 2-adic integer with binary digits `b`. -/
noncomputable def ofBits (b : ℕ → Bool) : ℤ_[2] := ∑' i, bv (b i) * 2 ^ i

lemma ofBits_rec (b : ℕ → Bool) : ofBits b = bv (b 0) + 2 * ofBits (fun i => b (i + 1)) := by
  rw [ofBits, (summable_ofBits b).tsum_eq_zero_add, ofBits,
    ← (summable_ofBits (fun i => b (i + 1))).tsum_mul_left]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  exact tsum_congr (fun i => by ring)

lemma par_ofBits (b : ℕ → Bool) : par (ofBits b) = if b 0 then 1 else 0 := by
  rw [ofBits_rec, par_add_two_mul, par_bv]

lemma shift_ofBits (b : ℕ → Bool) : shift (ofBits b) = ofBits (fun i => b (i + 1)) := by
  apply half_eq
  rw [par_ofBits]
  conv_rhs => rw [ofBits_rec b]
  cases b 0 <;> simp [bv]

lemma shift_iterate_ofBits (b : ℕ → Bool) :
    ∀ i, shift^[i] (ofBits b) = ofBits (fun j => b (j + i))
  | 0 => rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply', shift_iterate_ofBits b i, shift_ofBits]
    congr 1; funext j; congr 1; ring

theorem bits_ofBits (b : ℕ → Bool) : bits (ofBits b) = b := by
  funext i
  simp only [bits, shift_iterate_ofBits, par_ofBits, zero_add]
  cases b i <;> simp

lemma ofBits_partial (b : ℕ → Bool) : ∀ k : ℕ,
    ofBits b = ∑ i ∈ range k, bv (b i) * 2 ^ i + 2 ^ k * ofBits (fun j => b (j + k))
  | 0 => by simp
  | k + 1 => by
    rw [ofBits_partial b k, sum_range_succ, ofBits_rec (fun j => b (j + k))]
    simp only [zero_add]
    have e : (fun i => b (i + 1 + k)) = fun j => b (j + (k + 1)) := by funext j; congr 1; ring
    rw [e, pow_succ]
    ring

theorem ofBits_bits (y : ℤ_[2]) : ofBits (bits y) = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_dvd
  intro k
  have e := eq_bits_add y k
  refine ⟨ofBits (fun j => bits y (j + k)) - shift^[k] y, ?_⟩
  rw [ofBits_partial (bits y) k]
  linear_combination -e

lemma bits_dvd_iff : ∀ (k : ℕ) (b d : ℕ → Bool),
    (2 : ℤ_[2]) ^ k ∣ ∑ i ∈ range k, (bv (b i) - bv (d i)) * 2 ^ i ↔ ∀ i < k, b i = d i
  | 0, b, d => by simp
  | k + 1, b, d => by
    rw [sum_range_succ']
    simp only [pow_zero, mul_one, pow_succ]
    have e : ∑ i ∈ range k, (bv (b (i + 1)) - bv (d (i + 1))) * (2 ^ i * 2) =
        2 * ∑ i ∈ range k, (bv (b (i + 1)) - bv (d (i + 1))) * 2 ^ i := by
      rw [Finset.mul_sum]; exact sum_congr rfl (fun i _ => by ring)
    rw [e]
    constructor
    · intro h
      have h2 : (2 : ℤ_[2]) ∣ bv (b 0) - bv (d 0) :=
        (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_left _ _).trans h)
      have h0 : b 0 = d 0 := by
        rcases hb : b 0 <;> rcases hd : d 0 <;> rw [hb, hd] at h2 <;> simp [bv] at h2 ⊢ <;>
          · have := (two_dvd_iff _).1 h2; simp at this
      rw [h0, sub_self, add_zero, mul_comm (2 ^ k) 2,
        mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ_[2]) ≠ 0)] at h
      have ih := (bits_dvd_iff k (fun i => b (i + 1)) (fun i => d (i + 1))).1 h
      intro i hi
      rcases i with _ | i
      · exact h0
      · exact ih i (by omega)
    · intro h
      have hz : ∀ i ∈ range k, (bv (b (i + 1)) - bv (d (i + 1))) * 2 ^ i = 0 := by
        intro i hi; rw [h (i + 1) (by simp at hi; omega), sub_self, zero_mul]
      rw [sum_eq_zero hz, h 0 (by omega), sub_self, mul_zero, add_zero]
      exact dvd_zero _

theorem ofBits_preimage_ball (a : ℤ_[2]) (k : ℕ) :
    ofBits ⁻¹' closedBall a (rad k) = Set.pi (Finset.range k : Set ℕ) (fun i => {bits a i}) := by
  ext b
  rw [Set.mem_preimage, mem_ball_iff, Set.mem_pi]
  have e : ofBits b - a = ∑ i ∈ range k, (bv (b i) - bv (bits a i)) * 2 ^ i +
      2 ^ k * (ofBits (fun j => b (j + k)) - shift^[k] a) := by
    have h1 := ofBits_partial b k
    have h2 := eq_bits_add a k
    simp only [sub_mul, sum_sub_distrib]
    linear_combination h1 - h2
  rw [e, dvd_add_left (dvd_mul_right _ _), bits_dvd_iff]
  simp

/-! ## The Bernoulli measure -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool := (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

lemma coin_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  cases b <;> simp [coin]

instance : IsProbabilityMeasure coin := by
  constructor
  simp only [coin, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Independent fair coin flips indexed by `ℕ`. -/
noncomputable def bernoulli : Measure (ℕ → Bool) := Measure.infinitePi (fun _ => coin)

instance : IsProbabilityMeasure bernoulli := by unfold bernoulli; infer_instance

lemma bernoulli_box (d : ℕ → Bool) (k : ℕ) :
    bernoulli (Set.pi (Finset.range k : Set ℕ) (fun i => {d i})) = ((2 : ENNReal) ^ k)⁻¹ := by
  rw [bernoulli, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  simp only [coin_singleton, prod_const, card_range]
  rw [ENNReal.inv_pow]

/-- A finite measure giving every ball of radius `2^-k` mass `2^-k` is Haar measure. -/
theorem eq_μ_of_balls (ρ : Measure ℤ_[2]) [IsFiniteMeasure ρ]
    (h : ∀ a k, ρ (closedBall a (rad k)) = ((2 : ENNReal) ^ k)⁻¹) : ρ = μ := by
  refine ext_of_generate_finite cyls ms_eq isPiSystem_cyls ?_ ?_
  · rintro s ⟨a, k, rfl⟩; rw [h, μ_ball]
  · have hu : closedBall (0 : ℤ_[2]) (rad 0) = univ := by
      ext y; simp [rad, norm_le_one]
    rw [← hu, h, μ_ball]

lemma measurable_ofBits : Measurable ofBits := by
  have : @Measurable _ _ _ (MeasurableSpace.generateFrom cyls) ofBits := by
    refine measurable_generateFrom ?_
    rintro t ⟨a, k, rfl⟩
    rw [ofBits_preimage_ball]
    exact MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_singleton _)
  rwa [← ms_eq] at this

lemma measurableSet_par_eq_one : MeasurableSet {y : ℤ_[2] | par y = 1} := by
  have : {y : ℤ_[2] | par y = 1} = (closedBall 0 (rad 1))ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_compl_iff, mem_ball_iff, sub_zero, pow_one, two_dvd_iff]
    have := par_lt y
    rw [← ZMod.val_eq_zero]
    change par y = 1 ↔ ¬ par y = 0
    omega
  rw [this]
  exact (measurableSet_ball 0 1).compl

lemma measurable_bits : Measurable bits := by
  refine measurable_pi_iff.2 (fun i => ?_)
  have hm : Measurable (fun y : ℤ_[2] => decide (par y = 1)) := by
    refine measurable_to_countable' (fun v => ?_)
    cases v
    · have : (fun y : ℤ_[2] => decide (par y = 1)) ⁻¹' {false} = {y | par y = 1}ᶜ := by
        ext y; simp
      rw [this]; exact measurableSet_par_eq_one.compl
    · have : (fun y : ℤ_[2] => decide (par y = 1)) ⁻¹' {true} = {y | par y = 1} := by
        ext y; simp
      rw [this]; exact measurableSet_par_eq_one
  exact hm.comp (measurable_shift_iterate i)

theorem ofBits_measurePreserving : MeasurePreserving ofBits bernoulli μ := by
  refine ⟨measurable_ofBits, eq_μ_of_balls _ (fun a k => ?_)⟩
  rw [Measure.map_apply measurable_ofBits (measurableSet_ball a k), ofBits_preimage_ball,
    bernoulli_box]

theorem bits_measurePreserving : MeasurePreserving bits μ bernoulli := by
  refine ⟨measurable_bits, ?_⟩
  conv_lhs => rw [← ofBits_measurePreserving.map_eq]
  rw [Measure.map_map measurable_bits measurable_ofBits]
  have : bits ∘ ofBits = id := funext bits_ofBits
  rw [this, Measure.map_id]

/-! ## The parity sequence of `T` -/

/-- The parities along the `T`-orbit of `x`. -/
noncomputable def paritySeq (x : ℤ_[2]) : ℕ → Bool := fun i => decide (par (T^[i] x) = 1)

lemma paritySeq_eq (x : ℤ_[2]) : paritySeq x = bits (Q x) := by
  funext i
  simp only [paritySeq, bits, ← Q_iterate, par_Q]

theorem paritySeq_T (x : ℤ_[2]) : paritySeq (T x) = fun i => paritySeq x (i + 1) := by
  funext i
  unfold paritySeq; rw [Function.iterate_succ_apply]

/-- **The parities of a Haar-random 2-adic integer along its `T`-orbit are independent fair
coin flips.** -/
theorem paritySeq_measurePreserving : MeasurePreserving paritySeq μ bernoulli := by
  have : paritySeq = bits ∘ Qequiv := funext paritySeq_eq
  rw [this]
  exact bits_measurePreserving.comp (measurePreserving_isometryEquiv Qequiv)

theorem paritySeq_bijective : Function.Bijective paritySeq := by
  have : paritySeq = bits ∘ Qequiv := funext paritySeq_eq
  rw [this]
  refine (Function.bijective_iff_has_inverse.2 ⟨ofBits, ofBits_bits, bits_ofBits⟩).comp
    Qequiv.bijective

/-- The inverse of `paritySeq` is measure preserving as well. -/
theorem paritySeq_symm_measurePreserving :
    MeasurePreserving (Qequiv.symm ∘ ofBits) bernoulli μ :=
  (measurePreserving_isometryEquiv Qequiv.symm).comp ofBits_measurePreserving

theorem paritySeq_symm_apply (x : ℤ_[2]) : (Qequiv.symm ∘ ofBits) (paritySeq x) = x := by
  simp only [Function.comp, paritySeq_eq, ofBits_bits]
  exact Qequiv.symm_apply_apply x

end Collatz.TwoAdic
