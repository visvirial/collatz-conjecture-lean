import Collatz.Haar

/-!
# The 2-adic 3x+1 map is ergodic

For a ball `B = closedBall d (2^-k)` with `d < 2^k` and any measurable `E`,
`μ (B ∩ shift^[k] ⁻¹' E) = 2^-k μ E`: both sides are finite measures in `E` and they agree
on balls, since `B ∩ shift^[k] ⁻¹' closedBall c (2^-l) = closedBall (d + 2^k c) (2^-(k+l))`.

If `shift ⁻¹' S = S` then `shift^[k] ⁻¹' S = S`, so `μ (S ∩ B) = μ S μ B` for every ball `B`,
hence `μ.restrict S = μ S • μ` and `μ S = μ S ^ 2`. So the shift is ergodic, and by the
conjugacy `Q` so is `T` (Matthews and Watts 1984; Lagarias 1985).
-/

namespace Collatz.TwoAdic

open PadicInt MeasureTheory Metric Set Filter

lemma nat_eq_of_pow_dvd {k d e : ℕ} (hd : d < 2 ^ k) (he : e < 2 ^ k)
    (h : (2 : ℤ_[2]) ^ k ∣ (d : ℤ_[2]) - e) : d = e := by
  have h' : (2 : ℤ_[2]) ^ k ∣ (((d : ℤ) - e : ℤ) : ℤ_[2]) := by push_cast; exact h
  rw [← norm_le_iff_dvd, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, norm_int_le_pow_iff_dvd] at h'
  have hd' : (d : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hd
  have he' : (e : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast he
  have h0 : (d : ℤ) - e = 0 := Int.eq_zero_of_abs_lt_dvd (by exact_mod_cast h') (by
    rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg d : (0 : ℤ) ≤ d),
      (Nat.cast_nonneg e : (0 : ℤ) ≤ e)])
  omega

lemma ball_inter_shift_preimage (k l d : ℕ) (hd : d < 2 ^ k) (c : ℤ_[2]) :
    closedBall (d : ℤ_[2]) (rad k) ∩ shift^[k] ⁻¹' closedBall c (rad l) =
      closedBall ((d : ℤ_[2]) + 2 ^ k * c) (rad (k + l)) := by
  ext y
  obtain ⟨e, he, hy⟩ := eq_nat_add_shift_iterate k y
  rw [mem_inter_iff, mem_preimage, mem_ball_iff, mem_ball_iff, mem_ball_iff]
  generalize shift^[k] y = w at hy
  subst hy
  have e1 : (e : ℤ_[2]) + 2 ^ k * w - d = ((e : ℤ_[2]) - d) + 2 ^ k * w := by ring
  have e2 : (e : ℤ_[2]) + 2 ^ k * w - (d + 2 ^ k * c) = ((e : ℤ_[2]) - d) + 2 ^ k * (w - c) := by
    ring
  rw [e1, e2, pow_add]
  constructor
  · rintro ⟨h1, h2⟩
    have hed : e = d := nat_eq_of_pow_dvd he hd ((dvd_add_left (dvd_mul_right _ _)).1 h1)
    rw [hed, sub_self, zero_add]
    exact mul_dvd_mul_left _ h2
  · intro h
    have hk : (2 : ℤ_[2]) ^ k ∣ (e : ℤ_[2]) - d :=
      (dvd_add_left (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans h)
    have hed : e = d := nat_eq_of_pow_dvd he hd hk
    rw [hed, sub_self, zero_add] at h ⊢
    exact ⟨dvd_mul_right _ _, (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).1 h⟩

lemma measurable_shift_iterate (k : ℕ) : Measurable shift^[k] :=
  continuous_shift.measurable.iterate k

lemma measure_ball_inter_shift (k d : ℕ) (hd : d < 2 ^ k) {E : Set ℤ_[2]} (hE : MeasurableSet E) :
    μ (closedBall (d : ℤ_[2]) (rad k) ∩ shift^[k] ⁻¹' E) = ((2 : ENNReal) ^ k)⁻¹ * μ E := by
  set B := closedBall (d : ℤ_[2]) (rad k)
  have hm := measurable_shift_iterate k
  have key : (μ.restrict B).map shift^[k] = ((2 : ENNReal) ^ k)⁻¹ • μ := by
    refine ext_of_generate_finite cyls ms_eq isPiSystem_cyls ?_ ?_
    · rintro s ⟨c, l, rfl⟩
      rw [Measure.map_apply hm (measurableSet_ball _ _),
        Measure.restrict_apply (hm (measurableSet_ball _ _)), inter_comm,
        ball_inter_shift_preimage k l d hd c, μ_ball, smul_apply, μ_ball, smul_eq_mul,
        pow_add, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
    · rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, μ_ball, smul_apply,
        μ_univ, smul_eq_mul, mul_one]
  have := congrArg (fun ν : Measure ℤ_[2] => ν E) key
  rw [Measure.map_apply hm hE, Measure.restrict_apply (hm hE), smul_apply,
    smul_eq_mul] at this
  rw [inter_comm]
  exact this

lemma iterate_preimage_eq {S : Set ℤ_[2]} (h : shift ⁻¹' S = S) : ∀ k, shift^[k] ⁻¹' S = S
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ, preimage_comp, iterate_preimage_eq h k, h]

/-- The shift on `ℤ₂` is ergodic for Haar measure. -/
theorem shift_ergodic : Ergodic shift μ := by
  refine Ergodic.of_preimage_eq shift_measurePreserving (fun S hS hinv => ?_)
  have key : μ.restrict S = μ S • μ := by
    refine ext_of_generate_finite cyls ms_eq isPiSystem_cyls ?_ ?_
    · rintro s ⟨a, k, rfl⟩
      rw [Measure.restrict_apply (measurableSet_ball _ _), smul_apply, smul_eq_mul, μ_ball]
      have hb : closedBall a (rad k) = closedBall ((a.appr k : ℕ) : ℤ_[2]) (rad k) :=
        (IsUltrametricDist.closedBall_eq_of_mem (mem_ball_appr a k)).symm
      calc μ (closedBall a (rad k) ∩ S)
          = μ (closedBall ((a.appr k : ℕ) : ℤ_[2]) (rad k) ∩ shift^[k] ⁻¹' S) := by
            rw [hb, iterate_preimage_eq hinv k]
        _ = ((2 : ENNReal) ^ k)⁻¹ * μ S := measure_ball_inter_shift k _ (appr_lt a k) hS
        _ = μ S * ((2 : ENNReal) ^ k)⁻¹ := mul_comm _ _
    · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_apply, μ_univ,
        smul_eq_mul, mul_one]
  have hSS : μ S = μ S * μ S := by
    have := congrArg (fun ν : Measure ℤ_[2] => ν S) key
    rwa [Measure.restrict_apply hS, inter_self, smul_apply, smul_eq_mul] at this
  rw [eventuallyEmptyOrUniv_iff]
  rcases eq_or_ne (μ S) 0 with h0 | h0
  · right
    exact ae_iff.2 (by simpa using h0)
  · left
    have h1 : μ S = 1 := by
      have htop : μ S ≠ ⊤ := measure_ne_top μ S
      have : μ S * 1 = μ S * μ S := by rw [mul_one]; exact hSS
      exact ((ENNReal.mul_right_inj h0 htop).1 this).symm
    refine ae_iff.2 ?_
    have : μ Sᶜ = 0 := (prob_compl_eq_zero_iff hS).2 h1
    simpa [compl_def] using this

/-- The 2-adic 3x+1 map `T` is ergodic for Haar measure (Matthews and Watts 1984;
Lagarias 1985). -/
theorem T_ergodic : Ergodic T μ := by
  refine (measurePreserving_isometryEquiv Qequiv.symm).ergodic_of_ergodic_semiconj shift_ergodic
    T_measurePreserving.measurable (fun y => ?_)
  have := Qequiv_conj (Qequiv.symm y)
  rw [IsometryEquiv.apply_symm_apply] at this
  rw [← this, IsometryEquiv.symm_apply_apply]

end Collatz.TwoAdic
