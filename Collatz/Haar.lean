import Collatz.Periodic

/-!
# The 2-adic 3x+1 map preserves Haar measure

We equip `ℤ_[2]` with its Borel σ-algebra and the Haar probability measure `μ`.
The closed balls `closedBall a (2^-k)` (cylinder sets `a + 2^k ℤ₂`) form a π-system
generating the σ-algebra, and `μ (closedBall a (2^-k)) = 2^-k`. Hence a measurable map
preserves `μ` as soon as preimages of balls have the right measure. This holds for

* isometric bijections (`measurePreserving_isometryEquiv`), in particular `Q`;
* the shift, whose preimage of a ball of radius `2^-k` is two balls of radius `2^-(k+1)`.

Since `T = Q⁻¹ ∘ shift ∘ Q`, `T` preserves `μ` (`T_measurePreserving`) (Matthews and Watts 1984; Lagarias 1985).
-/

namespace Collatz.TwoAdic

open PadicInt MeasureTheory Metric Set

/-- The Borel σ-algebra on `ℤ_[2]`, scoped to `Collatz.TwoAdic` (Mathlib has none at this tag). -/
noncomputable scoped instance : MeasurableSpace ℤ_[2] := borel _
scoped instance : BorelSpace ℤ_[2] := ⟨rfl⟩

/-- The Haar probability measure on `ℤ_[2]`. -/
noncomputable def μ : Measure ℤ_[2] := Measure.addHaarMeasure ⊤

instance : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _

lemma μ_univ : μ univ = 1 := by
  have := Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts ℤ_[2]))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at this

instance : IsProbabilityMeasure μ := ⟨μ_univ⟩

/-! ## Balls -/

/-- The radius `2^-k`. -/
noncomputable def rad (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

lemma rad_pos (k : ℕ) : 0 < rad k := by unfold rad; positivity

lemma rad_anti {k l : ℕ} (h : k ≤ l) : rad l ≤ rad k :=
  zpow_le_zpow_right₀ (by norm_num) (by simpa using h)

lemma mem_ball_iff (a y : ℤ_[2]) (k : ℕ) :
    y ∈ closedBall a (rad k) ↔ (2 : ℤ_[2]) ^ k ∣ y - a := by
  rw [mem_closedBall, dist_eq_norm, rad, norm_le_iff_dvd]

lemma mem_ball_appr (x : ℤ_[2]) (k : ℕ) : x ∈ closedBall ((x.appr k : ℕ) : ℤ_[2]) (rad k) := by
  rw [mem_ball_iff]
  have := appr_spec k x
  rw [Ideal.mem_span_singleton] at this
  simpa using this

/-- Cylinder sets. -/
def cyls : Set (Set ℤ_[2]) := {s | ∃ a k, s = closedBall a (rad k)}

lemma isPiSystem_cyls : IsPiSystem cyls := by
  rintro s ⟨a, k, rfl⟩ t ⟨b, l, rfl⟩ ⟨x, hxs, hxt⟩
  rw [IsUltrametricDist.closedBall_eq_of_mem hxs, IsUltrametricDist.closedBall_eq_of_mem hxt]
  rcases le_total k l with h | h
  · rw [inter_eq_right.2 (closedBall_subset_closedBall (rad_anti h))]; exact ⟨x, l, rfl⟩
  · rw [inter_eq_left.2 (closedBall_subset_closedBall (rad_anti h))]; exact ⟨x, k, rfl⟩

lemma measurableSet_ball (a : ℤ_[2]) (k : ℕ) : MeasurableSet (closedBall a (rad k)) :=
  isClosed_closedBall.measurableSet

theorem ms_eq : (inferInstance : MeasurableSpace ℤ_[2]) = MeasurableSpace.generateFrom cyls := by
  apply le_antisymm
  · change borel ℤ_[2] ≤ _
    refine MeasurableSpace.generateFrom_le (fun U hU => ?_)
    have hU' : U = ⋃ p ∈ {p : ℕ × ℕ | closedBall ((p.2 : ℕ) : ℤ_[2]) (rad p.1) ⊆ U},
        closedBall ((p.2 : ℕ) : ℤ_[2]) (rad p.1) := by
      ext x
      constructor
      · intro hx
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
        obtain ⟨k, hk⟩ := exists_pow_neg_lt 2 hε
        have hxm := mem_ball_appr x k
        refine mem_biUnion (x := (k, x.appr k)) ?_ hxm
        show closedBall ((x.appr k : ℕ) : ℤ_[2]) (rad k) ⊆ U
        rw [IsUltrametricDist.closedBall_eq_of_mem hxm]
        refine (closedBall_subset_ball ?_).trans hball
        simpa [rad] using hk
      · intro hx
        simp only [mem_iUnion] at hx
        obtain ⟨p, hp, hxp⟩ := hx
        exact hp hxp
    rw [hU']
    exact MeasurableSet.biUnion (Set.to_countable _)
      (fun p _ => MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, k, rfl⟩
    exact measurableSet_ball a k

theorem μ_ball (a : ℤ_[2]) (k : ℕ) : μ (closedBall a (rad k)) = ((2 : ENNReal) ^ k)⁻¹ := by
  rw [Measure.addHaar_closedBall_center]
  have hcover : (univ : Set ℤ_[2]) =
      ⋃ n ∈ Finset.range (2 ^ k), closedBall ((n : ℕ) : ℤ_[2]) (rad k) := by
    ext x
    simp only [mem_univ, mem_iUnion, Finset.mem_range, true_iff]
    exact ⟨x.appr k, appr_lt x k, mem_ball_appr x k⟩
  have hdisj : (Finset.range (2 ^ k) : Set ℕ).PairwiseDisjoint
      (fun n : ℕ => closedBall ((n : ℕ) : ℤ_[2]) (rad k)) := by
    intro n hn m hm hnm
    rw [Function.onFun, Set.disjoint_left]
    intro y hy1 hy2
    rw [mem_ball_iff] at hy1 hy2
    have h : (2 : ℤ_[2]) ^ k ∣ (((m : ℤ) - n : ℤ) : ℤ_[2]) := by
      have := dvd_sub hy1 hy2
      push_cast
      convert this using 1; ring
    rw [← norm_le_iff_dvd, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, norm_int_le_pow_iff_dvd] at h
    simp only [Finset.coe_range, mem_Iio] at hn hm
    have hn' : (n : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hn
    have hm' : (m : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hm
    have h0 : (m : ℤ) - n = 0 := Int.eq_zero_of_abs_lt_dvd (by exact_mod_cast h) (by
      rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n),
        (Nat.cast_nonneg m : (0 : ℤ) ≤ m)])
    exact hnm (by omega)
  have h1 : (1 : ENNReal) = ∑ n ∈ Finset.range (2 ^ k), μ (closedBall (0 : ℤ_[2]) (rad k)) := by
    rw [← μ_univ, hcover, measure_biUnion_finset hdisj (fun n _ => measurableSet_ball _ _)]
    exact Finset.sum_congr rfl (fun n _ => Measure.addHaar_closedBall_center μ _ _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  push_cast at h1
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1.symm))

/-! ## Measure-preserving maps -/

theorem measurePreserving_of_balls {f : ℤ_[2] → ℤ_[2]} (hf : Measurable f)
    (h : ∀ a k, μ (f ⁻¹' closedBall a (rad k)) = μ (closedBall a (rad k))) :
    MeasurePreserving f μ μ := by
  refine ⟨hf, MeasureTheory.ext_of_generate_finite cyls ms_eq isPiSystem_cyls ?_ ?_⟩
  · rintro s ⟨a, k, rfl⟩
    rw [Measure.map_apply hf (measurableSet_ball a k)]
    exact h a k
  · rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ]

theorem measurePreserving_isometryEquiv (e : ℤ_[2] ≃ᵢ ℤ_[2]) : MeasurePreserving e μ μ := by
  refine measurePreserving_of_balls e.continuous.measurable (fun a k => ?_)
  rw [IsometryEquiv.preimage_closedBall, μ_ball, μ_ball]

lemma continuous_of_dvd {f : ℤ_[2] → ℤ_[2]}
    (h : ∀ k x y, (2 : ℤ_[2]) ^ (k + 1) ∣ x - y → (2 : ℤ_[2]) ^ k ∣ f x - f y) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨k, hk⟩ := exists_pow_neg_lt 2 hε
  refine ⟨rad (k + 1), rad_pos _, fun y hy => ?_⟩
  have hd : (2 : ℤ_[2]) ^ (k + 1) ∣ y - x := (mem_ball_iff x y (k + 1)).1 (mem_closedBall.2 hy.le)
  have := (mem_ball_iff (f x) (f y) k).2 (h k y x hd)
  exact lt_of_le_of_lt (mem_closedBall.1 this) (by simpa [rad] using hk)

lemma par_eq_of_two_dvd {x y : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x - y) : par x = par y := by
  apply par_eq_of_toZMod
  have := (two_dvd_iff _).1 h
  rw [map_sub, sub_eq_zero] at this
  exact this

lemma shift_dvd (k : ℕ) (x y : ℤ_[2]) (h : (2 : ℤ_[2]) ^ (k + 1) ∣ x - y) :
    (2 : ℤ_[2]) ^ k ∣ shift x - shift y := by
  have hp : par x = par y := par_eq_of_two_dvd ((dvd_pow_self 2 (by omega)).trans h)
  have e : 2 * (shift x - shift y) = x - y := by
    rw [mul_sub, two_mul_shift, two_mul_shift, hp]; ring
  rw [← e, pow_succ', mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ_[2]) ≠ 0)] at h
  exact h

lemma continuous_shift : Continuous shift := continuous_of_dvd shift_dvd

lemma mem_shift_preimage (a y : ℤ_[2]) (k : ℕ) :
    y ∈ shift ⁻¹' closedBall a (rad k) ↔
      y ∈ closedBall (2 * a) (rad (k + 1)) ∨ y ∈ closedBall (2 * a + 1) (rad (k + 1)) := by
  rw [mem_preimage, mem_ball_iff, mem_ball_iff, mem_ball_iff]
  have key : ∀ b : ℕ, b < 2 → ((2 : ℤ_[2]) ^ (k + 1) ∣ y - (2 * a + b) ↔
      par y = b ∧ (2 : ℤ_[2]) ^ k ∣ shift y - a) := by
    intro b hb
    have e : 2 * (shift y - a) = y - par y - 2 * a := by rw [mul_sub, two_mul_shift]
    constructor
    · intro h
      have hp : par y = b := by
        have := par_eq_of_two_dvd ((dvd_pow_self 2 (by omega)).trans h)
        rw [this, show 2 * a + (b : ℤ_[2]) = (b : ℤ_[2]) + 2 * a by ring, par_add_two_mul,
          par_natCast, Nat.mod_eq_of_lt hb]
      refine ⟨hp, ?_⟩
      rw [← mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ_[2]) ≠ 0), ← pow_succ', e, hp]
      convert h using 1; ring
    · rintro ⟨hp, h⟩
      rw [← mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ_[2]) ≠ 0), ← pow_succ', e, hp] at h
      convert h using 1; ring
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  simp only [Nat.cast_zero, add_zero, Nat.cast_one] at k0 k1
  rw [k0, k1]
  have := par_lt y
  constructor
  · intro h
    interval_cases hy : par y
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, h⟩
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h

theorem shift_measurePreserving : MeasurePreserving shift μ μ := by
  refine measurePreserving_of_balls continuous_shift.measurable (fun a k => ?_)
  have hset : shift ⁻¹' closedBall a (rad k) =
      closedBall (2 * a) (rad (k + 1)) ∪ closedBall (2 * a + 1) (rad (k + 1)) := by
    ext y; rw [mem_union]; exact mem_shift_preimage a y k
  have hdisj : Disjoint (closedBall (2 * a) (rad (k + 1))) (closedBall (2 * a + 1) (rad (k + 1))) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    rw [mem_ball_iff] at h1 h2
    have h := dvd_sub h1 h2
    have e1 : y - 2 * a - (y - (2 * a + 1)) = 1 := by ring
    rw [e1] at h
    have h' : (2 : ℤ_[2]) ∣ 1 := (dvd_pow_self (2 : ℤ_[2]) (Nat.succ_ne_zero k)).trans h
    have := (two_dvd_iff 1).1 h'
    rw [map_one] at this
    exact one_ne_zero this
  rw [hset, measure_union hdisj (measurableSet_ball _ _), μ_ball, μ_ball, μ_ball, pow_succ,
    ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), ← two_mul, ← mul_assoc,
    mul_right_comm, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The 2-adic 3x+1 map preserves Haar measure (Matthews and Watts 1984; Lagarias 1985). -/
theorem T_measurePreserving : MeasurePreserving T μ μ := by
  have hT : T = Qequiv.symm ∘ shift ∘ Qequiv := by
    funext x
    simp only [Function.comp]
    rw [← Qequiv_conj, IsometryEquiv.symm_apply_apply]
  rw [hT]
  exact (measurePreserving_isometryEquiv _).comp
    (shift_measurePreserving.comp (measurePreserving_isometryEquiv _))

end Collatz.TwoAdic
