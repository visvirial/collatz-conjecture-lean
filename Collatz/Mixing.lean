import Collatz.Ergodic

/-!
# The 2-adic 3x+1 map is exact and strongly mixing

Let `B = closedBall d (2^-k)` with `d < 2^k`. For `n ≥ k` and measurable `E`,
`B ∩ shift^[n] ⁻¹' E = B ∩ shift^[k] ⁻¹' (shift^[n-k] ⁻¹' E)`, so `μ (B ∩ shift^[n] ⁻¹' E) = μ B μ E`
(`shift_mixing_ball`). The same then holds for every finite union `A` of balls of radius `2^-k`
(`measure_cyl_inter`). These sets form a ring generating the σ-algebra, so any measurable set is
approximated by them in measure, which gives strong mixing (`shift_mixing`).

If `S = shift^[n] ⁻¹' E_n` for every `n`, then `μ (B ∩ S) = μ B μ S` for every ball `B`, hence
`μ S ∈ {0, 1}`: the shift is exact (`shift_exact`). Via the conjugacy `Q`, `T` is exact
(`T_exact`) and strongly mixing (`T_mixing`).
-/

namespace Collatz.TwoAdic

open PadicInt MeasureTheory Metric Set Filter
open scoped symmDiff Topology

/-! ## Mixing on balls -/

lemma shift_iterate_preimage_of_le {k n : ℕ} (hn : k ≤ n) (E : Set ℤ_[2]) :
    shift^[n] ⁻¹' E = shift^[k] ⁻¹' (shift^[n - k] ⁻¹' E) := by
  rw [← preimage_comp, ← Function.iterate_add, Nat.sub_add_cancel hn]

/-- Balls of radius `2^-k` are independent of `shift^[n] ⁻¹' E` for `n ≥ k`. -/
theorem shift_mixing_ball {k d : ℕ} (hd : d < 2 ^ k) {E : Set ℤ_[2]} (hE : MeasurableSet E)
    {n : ℕ} (hn : k ≤ n) :
    μ (closedBall (d : ℤ_[2]) (rad k) ∩ shift^[n] ⁻¹' E) =
      μ (closedBall (d : ℤ_[2]) (rad k)) * μ E := by
  rw [shift_iterate_preimage_of_le hn,
    measure_ball_inter_shift k d hd (measurable_shift_iterate (n - k) hE),
    (shift_measurePreserving.iterate (n - k)).measure_preimage hE.nullMeasurableSet, μ_ball]

/-- The same for balls with an arbitrary center. -/
theorem shift_mixing_ball' (a : ℤ_[2]) (k : ℕ) {E : Set ℤ_[2]} (hE : MeasurableSet E)
    {n : ℕ} (hn : k ≤ n) :
    μ (closedBall a (rad k) ∩ shift^[n] ⁻¹' E) = μ (closedBall a (rad k)) * μ E := by
  have hb : closedBall a (rad k) = closedBall ((a.appr k : ℕ) : ℤ_[2]) (rad k) :=
    (IsUltrametricDist.closedBall_eq_of_mem (mem_ball_appr a k)).symm
  rw [hb]
  exact shift_mixing_ball (appr_lt a k) hE hn

/-! ## Exactness -/

/-- The shift on `ℤ₂` is exact: every set in the tail σ-algebra has measure `0` or `1`. -/
theorem shift_exact {S : Set ℤ_[2]}
    (hS : ∀ n, ∃ E, MeasurableSet E ∧ S = shift^[n] ⁻¹' E) : μ S = 0 ∨ μ S = 1 := by
  have hSm : MeasurableSet S := by
    obtain ⟨E, hE, h⟩ := hS 0
    rw [h, Function.iterate_zero, preimage_id]; exact hE
  have key : μ.restrict S = μ S • μ := by
    refine ext_of_generate_finite cyls ms_eq isPiSystem_cyls ?_ ?_
    · rintro s ⟨a, k, rfl⟩
      obtain ⟨E, hE, h⟩ := hS k
      have hμ : μ S = μ E := by
        rw [h]; exact shift_measurePreserving.iterate k |>.measure_preimage hE.nullMeasurableSet
      rw [Measure.restrict_apply (measurableSet_ball _ _), smul_apply, smul_eq_mul, hμ, h,
        shift_mixing_ball' a k hE le_rfl, mul_comm]
    · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_apply, μ_univ,
        smul_eq_mul, mul_one]
  have hSS : μ S = μ S * μ S := by
    have := congrArg (fun ν : Measure ℤ_[2] => ν S) key
    rwa [Measure.restrict_apply hSm, inter_self, smul_apply, smul_eq_mul] at this
  rcases eq_or_ne (μ S) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have htop : μ S ≠ ⊤ := measure_ne_top μ S
    have : μ S * 1 = μ S * μ S := by rw [mul_one]; exact hSS
    exact ((ENNReal.mul_right_inj h0 htop).1 this).symm

lemma Qequiv_iterate (n : ℕ) (x : ℤ_[2]) : Qequiv (T^[n] x) = shift^[n] (Qequiv x) :=
  (Function.Semiconj.iterate_right (f := Qequiv) Qequiv_conj n) x

lemma T_iterate_symm (n : ℕ) (y : ℤ_[2]) :
    T^[n] (Qequiv.symm y) = Qequiv.symm (shift^[n] y) := by
  apply Qequiv.injective
  rw [Qequiv_iterate, IsometryEquiv.apply_symm_apply, IsometryEquiv.apply_symm_apply]

lemma preimage_T_iterate (n : ℕ) (E : Set ℤ_[2]) :
    Qequiv.symm ⁻¹' (T^[n] ⁻¹' E) = shift^[n] ⁻¹' (Qequiv.symm ⁻¹' E) := by
  ext y
  simp only [mem_preimage, T_iterate_symm]

/-- The 2-adic 3x+1 map `T` is exact: every set in its tail σ-algebra has measure `0` or `1`. -/
theorem T_exact {S : Set ℤ_[2]}
    (hS : ∀ n, ∃ E, MeasurableSet E ∧ S = T^[n] ⁻¹' E) : μ S = 0 ∨ μ S = 1 := by
  have hSm : MeasurableSet S := by
    obtain ⟨E, hE, h⟩ := hS 0
    rw [h, Function.iterate_zero, preimage_id]; exact hE
  have hμ : μ (Qequiv.symm ⁻¹' S) = μ S :=
    (measurePreserving_isometryEquiv Qequiv.symm).measure_preimage hSm.nullMeasurableSet
  rw [← hμ]
  refine shift_exact (fun n => ?_)
  obtain ⟨E, hE, h⟩ := hS n
  exact ⟨Qequiv.symm ⁻¹' E, Qequiv.symm.continuous.measurable hE, by
    rw [h, preimage_T_iterate]⟩

/-! ## Finite unions of balls -/

/-- `A` is a union of balls of radius `2^-k`. -/
def IsCyl (k : ℕ) (A : Set ℤ_[2]) : Prop :=
  ∀ y z : ℤ_[2], (2 : ℤ_[2]) ^ k ∣ y - z → y ∈ A → z ∈ A

lemma IsCyl.mono {k l : ℕ} {A : Set ℤ_[2]} (h : k ≤ l) (hA : IsCyl k A) : IsCyl l A :=
  fun y z hyz => hA y z ((pow_dvd_pow 2 h).trans hyz)

lemma isCyl_ball (a : ℤ_[2]) (k : ℕ) : IsCyl k (closedBall a (rad k)) := by
  intro y z h hy
  rw [mem_ball_iff] at hy ⊢
  have := dvd_sub hy h
  rwa [show y - a - (y - z) = z - a by ring] at this

/-- The residues `d < 2^k` with `d ∈ A`. -/
noncomputable def cylSet (k : ℕ) (A : Set ℤ_[2]) : Finset ℕ := by
  classical exact (Finset.range (2 ^ k)).filter (fun d => ((d : ℕ) : ℤ_[2]) ∈ A)

lemma mem_cylSet {k : ℕ} {A : Set ℤ_[2]} {d : ℕ} :
    d ∈ cylSet k A ↔ d < 2 ^ k ∧ ((d : ℕ) : ℤ_[2]) ∈ A := by
  unfold cylSet
  simp

lemma cyl_eq {k : ℕ} {A : Set ℤ_[2]} (hA : IsCyl k A) :
    A = ⋃ d ∈ cylSet k A, closedBall ((d : ℕ) : ℤ_[2]) (rad k) := by
  ext y
  simp only [mem_iUnion, exists_prop, mem_cylSet]
  constructor
  · intro hy
    have hm := mem_ball_appr y k
    exact ⟨y.appr k, ⟨appr_lt y k, hA y _ ((mem_ball_iff _ _ _).1 hm) hy⟩, hm⟩
  · rintro ⟨d, ⟨-, hd⟩, hy⟩
    exact hA _ y (dvd_sub_comm.1 ((mem_ball_iff _ _ _).1 hy)) hd

lemma pairwiseDisjoint_balls (k : ℕ) (s : Finset ℕ) (hs : ∀ d ∈ s, d < 2 ^ k) :
    (s : Set ℕ).PairwiseDisjoint (fun d : ℕ => closedBall ((d : ℕ) : ℤ_[2]) (rad k)) := by
  intro d hd e he hde
  rw [Function.onFun, Set.disjoint_left]
  intro y h1 h2
  rw [mem_ball_iff] at h1 h2
  have h := dvd_sub h2 h1
  rw [show y - (e : ℤ_[2]) - (y - d) = d - e by ring] at h
  exact hde (nat_eq_of_pow_dvd (hs d hd) (hs e he) h)

lemma measurableSet_cyl {k : ℕ} {A : Set ℤ_[2]} (hA : IsCyl k A) : MeasurableSet A := by
  rw [cyl_eq hA]
  exact Finset.measurableSet_biUnion _ (fun d _ => measurableSet_ball _ _)

/-- Unions of balls of radius `2^-k` are independent of `shift^[n] ⁻¹' E` for `n ≥ k`. -/
theorem measure_cyl_inter {k : ℕ} {A : Set ℤ_[2]} (hA : IsCyl k A) {E : Set ℤ_[2]}
    (hE : MeasurableSet E) {n : ℕ} (hn : k ≤ n) :
    μ (A ∩ shift^[n] ⁻¹' E) = μ A * μ E := by
  have hs : ∀ d ∈ cylSet k A, d < 2 ^ k := fun d hd => (mem_cylSet.1 hd).1
  have hdisj := pairwiseDisjoint_balls k (cylSet k A) hs
  have hX := measurable_shift_iterate n hE
  have h1 : μ A = ∑ d ∈ cylSet k A, μ (closedBall ((d : ℕ) : ℤ_[2]) (rad k)) := by
    conv_lhs => rw [cyl_eq hA]
    exact measure_biUnion_finset hdisj (fun d _ => measurableSet_ball _ _)
  have h2 : μ (A ∩ shift^[n] ⁻¹' E) =
      ∑ d ∈ cylSet k A, μ (closedBall ((d : ℕ) : ℤ_[2]) (rad k) ∩ shift^[n] ⁻¹' E) := by
    conv_lhs => rw [cyl_eq hA, iUnion₂_inter]
    exact measure_biUnion_finset (hdisj.mono (fun d => inter_subset_left))
      (fun d _ => (measurableSet_ball _ _).inter hX)
  rw [h2, h1, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun d hd => shift_mixing_ball (hs d hd) hE hn)

/-- The finite unions of balls. -/
def cylSets : Set (Set ℤ_[2]) := {A | ∃ k, IsCyl k A}

lemma isSetRing_cylSets : IsSetRing cylSets where
  empty_mem := ⟨0, fun _ _ _ h => h⟩
  union_mem := by
    rintro s t ⟨k, hs⟩ ⟨l, ht⟩
    refine ⟨max k l, fun y z h hy => ?_⟩
    rcases hy with hy | hy
    · exact Or.inl ((hs.mono (le_max_left k l)) y z h hy)
    · exact Or.inr ((ht.mono (le_max_right k l)) y z h hy)
  sdiff_mem := by
    rintro s t ⟨k, hs⟩ ⟨l, ht⟩
    refine ⟨max k l, fun y z h hy => ⟨(hs.mono (le_max_left k l)) y z h hy.1, fun hz => ?_⟩⟩
    exact hy.2 ((ht.mono (le_max_right k l)) z y (dvd_sub_comm.1 h) hz)

lemma ms_eq_cylSets :
    (inferInstance : MeasurableSpace ℤ_[2]) = MeasurableSpace.generateFrom cylSets := by
  apply le_antisymm
  · rw [ms_eq]
    refine MeasurableSpace.generateFrom_mono ?_
    rintro s ⟨a, k, rfl⟩
    exact ⟨k, isCyl_ball a k⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨k, hs⟩
    exact measurableSet_cyl hs

lemma measure_inter_le_add_symmDiff (s t u : Set ℤ_[2]) :
    μ (s ∩ u) ≤ μ (t ∩ u) + μ (t ∆ s) := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro y ⟨hys, hyu⟩
  by_cases hyt : y ∈ t
  · exact Or.inl ⟨hyt, hyu⟩
  · exact Or.inr (mem_symmDiff.2 (Or.inr ⟨hys, hyt⟩))

/-! ## Strong mixing -/

/-- The shift on `ℤ₂` is strongly mixing for Haar measure. -/
theorem shift_mixing {A B : Set ℤ_[2]} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n => μ (A ∩ shift^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B)) := by
  rw [ENNReal.tendsto_nhds (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  intro ε hε
  have h'C : ∃ D : Set (Set ℤ_[2]), D.Countable ∧ D ⊆ cylSets ∧ μ (⋃₀ D)ᶜ = 0 :=
    ⟨{univ}, countable_singleton _, singleton_subset_iff.2 ⟨0, fun _ _ _ _ => mem_univ _⟩,
      by simp⟩
  obtain ⟨t, ⟨k, ht⟩, hts⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_cylSets h'C ms_eq_cylSets hA (ENNReal.half_pos hε.ne')
  rw [eventually_atTop]
  refine ⟨k, fun n hn => ?_⟩
  set X := shift^[n] ⁻¹' B
  have htX : μ (t ∩ X) = μ t * μ B := measure_cyl_inter ht hB hn
  set δ := μ (t ∆ A) with hδ
  have hδ' : μ (A ∆ t) = δ := by rw [symmDiff_comm]
  have h1 : μ (A ∩ X) ≤ μ (t ∩ X) + δ := measure_inter_le_add_symmDiff A t X
  have h2 : μ (t ∩ X) ≤ μ (A ∩ X) + δ := hδ' ▸ measure_inter_le_add_symmDiff t A X
  have h3 : μ A ≤ μ t + δ := by
    simpa only [inter_univ] using measure_inter_le_add_symmDiff A t univ
  have h4 : μ t ≤ μ A + δ := by
    simpa only [inter_univ, hδ'] using measure_inter_le_add_symmDiff t A univ
  have hB1 : μ B ≤ 1 := prob_le_one
  have hδB : δ * μ B ≤ δ := mul_le_of_le_one_right zero_le hB1
  have hδε : δ + δ ≤ ε := by
    calc δ + δ ≤ ε / 2 + ε / 2 := add_le_add hts.le hts.le
      _ = ε := ENNReal.add_halves ε
  constructor
  · rw [tsub_le_iff_right]
    calc μ A * μ B ≤ (μ t + δ) * μ B := by gcongr
      _ = μ (t ∩ X) + δ * μ B := by rw [add_mul, htX]
      _ ≤ (μ (A ∩ X) + δ) + δ := add_le_add h2 hδB
      _ = μ (A ∩ X) + (δ + δ) := add_assoc _ _ _
      _ ≤ μ (A ∩ X) + ε := by gcongr
  · calc μ (A ∩ X) ≤ μ t * μ B + δ := htX ▸ h1
      _ ≤ (μ A + δ) * μ B + δ := by gcongr
      _ = μ A * μ B + δ * μ B + δ := by rw [add_mul]
      _ ≤ μ A * μ B + δ + δ := by gcongr
      _ = μ A * μ B + (δ + δ) := add_assoc _ _ _
      _ ≤ μ A * μ B + ε := by gcongr

/-- The 2-adic 3x+1 map `T` is strongly mixing for Haar measure. -/
theorem T_mixing {A B : Set ℤ_[2]} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n => μ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B)) := by
  have hQ := measurePreserving_isometryEquiv Qequiv.symm
  have hm : Measurable Qequiv.symm := Qequiv.symm.continuous.measurable
  have e : ∀ n, μ (A ∩ T^[n] ⁻¹' B) =
      μ ((Qequiv.symm ⁻¹' A) ∩ shift^[n] ⁻¹' (Qequiv.symm ⁻¹' B)) := by
    intro n
    rw [← preimage_T_iterate, ← preimage_inter]
    exact (hQ.measure_preimage
      (hA.inter (T_measurePreserving.measurable.iterate n hB)).nullMeasurableSet).symm
  simp only [e]
  rw [← hQ.measure_preimage hA.nullMeasurableSet, ← hQ.measure_preimage hB.nullMeasurableSet]
  exact shift_mixing (hm hA) (hm hB)

end Collatz.TwoAdic
