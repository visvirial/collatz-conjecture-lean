import Collatz.Lagarias

/-!
# The 3x+1 map on the 2-adic integers (Lagarias 1985)

We extend `T` to `ℤ₂ = ℤ_[2]` by `T x = (x + par x * (2x + 1)) / 2`, i.e. `x / 2` or
`(3x + 1) / 2`, and define the conjugacy map

  `Q x = ∑ i, par (T^i x) 2^i`.

Main results:
* `T_natCast`: `T` extends the accelerated Collatz map on `ℕ`;
* `Q_conj`: `Q (T x) = shift (Q x)`, where `shift y = (y - par y) / 2`;
* `Q_isometry`, `Q_bijective`: `Q` is an isometric bijection of `ℤ₂`,
  packaged as `Qequiv : ℤ_[2] ≃ᵢ ℤ_[2]`.

So `T` is conjugate to the shift, the model of a Bernoulli process.
-/

namespace Collatz.TwoAdic

open PadicInt Finset

/-! ## Parity and halving -/

/-- The parity of a 2-adic integer, `0` or `1`. -/
noncomputable def par (x : ℤ_[2]) : ℕ := (toZMod x).val

lemma par_lt (x : ℤ_[2]) : par x < 2 := ZMod.val_lt _

lemma toZMod_par (x : ℤ_[2]) : toZMod ((par x : ℕ) : ℤ_[2]) = toZMod x := by
  rw [map_natCast, par, ZMod.natCast_zmod_val]

lemma two_dvd_iff (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ toZMod x = 0 := by
  rw [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  norm_num

lemma toZMod_two_mul (A : ℤ_[2]) : toZMod (2 * A) = 0 :=
  (two_dvd_iff _).1 (dvd_mul_right 2 A)

lemma par_eq_of_toZMod {x y : ℤ_[2]} (h : toZMod x = toZMod y) : par x = par y := by
  rw [par, par, h]

lemma par_natCast (n : ℕ) : par (n : ℤ_[2]) = n % 2 := by
  rw [par, map_natCast, ZMod.val_natCast]

open Classical in
/-- `x / 2` for even `x` (junk value `0` otherwise). -/
noncomputable def half (x : ℤ_[2]) : ℤ_[2] := if h : (2 : ℤ_[2]) ∣ x then h.choose else 0

lemma two_mul_half {x : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x) : 2 * half x = x := by
  simp only [half, h, ↓reduceDIte]; exact h.choose_spec.symm

lemma half_eq {x y : ℤ_[2]} (h : 2 * y = x) : half x = y :=
  mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[2]) ≠ 0) (by rw [two_mul_half ⟨y, h.symm⟩, h])

/-! ## The map `T` -/

lemma dvd_T_arg (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x + (par x : ℤ_[2]) * (2 * x + 1) := by
  rw [two_dvd_iff, map_add, map_mul, toZMod_par, map_add, map_mul, map_one]
  generalize toZMod x = t
  have h2 : (toZMod (2 : ℤ_[2]) : ZMod 2) = 2 := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]; rfl
  rw [h2]
  revert t; decide

/-- The 2-adic extension of the accelerated Collatz map. -/
noncomputable def T (x : ℤ_[2]) : ℤ_[2] := half (x + (par x : ℤ_[2]) * (2 * x + 1))

lemma two_mul_T (x : ℤ_[2]) : 2 * T x = x + (par x : ℤ_[2]) * (2 * x + 1) :=
  two_mul_half (dvd_T_arg x)

theorem T_natCast (n : ℕ) : T (n : ℤ_[2]) = (kstepT n : ℤ_[2]) := by
  apply half_eq
  rw [par_natCast]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have e : 2 * kstepT n = n := by rw [kstepT_of_even h]; omega
    have e' : (2 : ℤ_[2]) * (kstepT n : ℕ) = n := by exact_mod_cast e
    rw [h, e']; simp
  · have e : 2 * kstepT n = 3 * n + 1 := by rw [kstepT_of_odd h]; omega
    rw [h]
    have e' : (2 : ℤ_[2]) * (kstepT n : ℕ) = 3 * (n : ℤ_[2]) + 1 := by exact_mod_cast e
    rw [e']; push_cast; ring

theorem T_iterate_natCast (n i : ℕ) : T^[i] (n : ℤ_[2]) = ((kstepT^[i] n : ℕ) : ℤ_[2]) := by
  induction i generalizing n with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_natCast, ih]

lemma par_add_two_mul (w A : ℤ_[2]) : par (w + 2 * A) = par w :=
  par_eq_of_toZMod (by rw [map_add, toZMod_two_mul, add_zero])

lemma T_add_two_mul (w A : ℤ_[2]) : T (w + 2 * A) = T w + (1 + 2 * (par w : ℤ_[2])) * A := by
  apply half_eq
  rw [mul_add, two_mul_T, par_add_two_mul]
  ring

/-- Number of odd points among `x, T x, …, T^(j-1) x`. -/
noncomputable def oddCount2 (j : ℕ) (x : ℤ_[2]) : ℕ := ∑ i ∈ range j, par (T^[i] x)

lemma oddCount2_succ (j : ℕ) (x : ℤ_[2]) : oddCount2 (j + 1) x = oddCount2 j x + par (T^[j] x) :=
  sum_range_succ _ _

lemma T_iterate_affine (x z : ℤ_[2]) (k : ℕ) : ∀ j ≤ k,
    T^[j] (x + 2 ^ k * z) = T^[j] x + 2 ^ (k - j) * 3 ^ oddCount2 j x * z := by
  intro j
  induction j with
  | zero => intro; simp [oddCount2]
  | succ j ih =>
    intro hj
    obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega), he,
      show k - (j + 1) = e by omega, oddCount2_succ,
      show (2 : ℤ_[2]) ^ (e + 1) * 3 ^ oddCount2 j x * z = 2 * (2 ^ e * 3 ^ oddCount2 j x * z)
        by ring, T_add_two_mul]
    have hp := par_lt (T^[j] x)
    interval_cases h : par (T^[j] x) <;> push_cast <;> ring

lemma par_iterate_affine (x z : ℤ_[2]) {k i : ℕ} (hi : i < k) :
    par (T^[i] (x + 2 ^ k * z)) = par (T^[i] x) := by
  rw [T_iterate_affine x z k i hi.le]
  obtain ⟨e, he⟩ : ∃ e, k - i = e + 1 := ⟨k - i - 1, by omega⟩
  rw [he, show (2 : ℤ_[2]) ^ (e + 1) * 3 ^ oddCount2 i x * z = 2 * (2 ^ e * 3 ^ oddCount2 i x * z)
    by ring, par_add_two_mul]

/-! ## The conjugacy map `Q` -/

lemma summable_Q (x : ℤ_[2]) : Summable (fun i => (par (T^[i] x) : ℤ_[2]) * 2 ^ i) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [norm_mul, norm_pow, show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, norm_p]
  calc ‖((par (T^[i] x) : ℕ) : ℤ_[2])‖ * ((2 : ℕ) : ℝ)⁻¹ ^ i ≤ 1 * ((2 : ℕ) : ℝ)⁻¹ ^ i :=
        mul_le_mul_of_nonneg_right (norm_le_one _) (by positivity)
    _ = (1 / 2) ^ i := by norm_num

/-- Lagarias' conjugacy map: the parity sequence of `x`, read as a 2-adic integer. -/
noncomputable def Q (x : ℤ_[2]) : ℤ_[2] := ∑' i, (par (T^[i] x) : ℤ_[2]) * 2 ^ i

theorem Q_rec (x : ℤ_[2]) : Q x = par x + 2 * Q (T x) := by
  rw [Q, (summable_Q x).tsum_eq_zero_add, Q, ← (summable_Q (T x)).tsum_mul_left]
  simp only [Function.iterate_zero, id, pow_zero, mul_one, Function.iterate_succ_apply, pow_succ]
  congr 1
  exact tsum_congr (fun i => by ring)

/-- Partial sums of `Q`. -/
noncomputable def S (k : ℕ) (x : ℤ_[2]) : ℤ_[2] := ∑ i ∈ range k, (par (T^[i] x) : ℤ_[2]) * 2 ^ i

lemma S_succ (k : ℕ) (x : ℤ_[2]) : S (k + 1) x = S k x + (par (T^[k] x) : ℤ_[2]) * 2 ^ k :=
  sum_range_succ _ _

theorem Q_partial (x : ℤ_[2]) : ∀ k, Q x = S k x + 2 ^ k * Q (T^[k] x)
  | 0 => by simp [S]
  | k + 1 => by
    rw [Q_partial x k, Q_rec (T^[k] x), S_succ, Function.iterate_succ_apply']
    ring

lemma S_natCast (k n : ℕ) : S k (n : ℤ_[2]) = ((parityVec k n : ℕ) : ℤ_[2]) := by
  simp only [S, parityVec, T_iterate_natCast, par_natCast]
  push_cast
  rfl

lemma S_eq_of_dvd {x y : ℤ_[2]} {k : ℕ} (h : (2 : ℤ_[2]) ^ k ∣ x - y) : S k x = S k y := by
  obtain ⟨z, hz⟩ := h
  have hx : x = y + 2 ^ k * z := by rw [← hz]; ring
  refine sum_congr rfl (fun i hi => ?_)
  rw [hx, par_iterate_affine y z (mem_range.1 hi)]

lemma toZMod_Q (x : ℤ_[2]) : toZMod (Q x) = toZMod x := by
  rw [Q_rec, map_add, toZMod_two_mul, add_zero, toZMod_par]

lemma par_Q (x : ℤ_[2]) : par (Q x) = par x := par_eq_of_toZMod (toZMod_Q x)

/-- The shift on `ℤ₂`: drop the last binary digit. -/
noncomputable def shift (y : ℤ_[2]) : ℤ_[2] := half (y - par y)

/-- **Conjugacy**: `Q ∘ T = shift ∘ Q`. -/
theorem Q_conj (x : ℤ_[2]) : Q (T x) = shift (Q x) := by
  rw [shift, par_Q]
  exact (half_eq (by rw [Q_rec x]; ring)).symm

/-! ## `Q` is an isometry -/

theorem pow_dvd_Q_sub_iff (k : ℕ) (x y : ℤ_[2]) :
    (2 : ℤ_[2]) ^ k ∣ Q x - Q y ↔ (2 : ℤ_[2]) ^ k ∣ x - y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (ih x y).1 ((pow_dvd_pow 2 (Nat.le_succ k)).trans h)
      have hx : x = y + 2 ^ k * z := by rw [← hz]; ring
      have hS := S_eq_of_dvd ⟨z, hz⟩
      rw [Q_partial x k, Q_partial y k, hS, add_sub_add_left_eq_sub, ← mul_sub, pow_succ,
        mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)] at h
      rw [two_dvd_iff, map_sub, toZMod_Q, toZMod_Q, hx, T_iterate_affine y z k k le_rfl,
        Nat.sub_self, pow_zero, one_mul, map_add, add_sub_cancel_left, map_mul, map_pow] at h
      have h3 : toZMod (3 : ℤ_[2]) = 1 := by
        rw [show (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) by norm_num, map_natCast]; rfl
      rw [h3, one_pow, one_mul] at h
      obtain ⟨w, hw⟩ := (two_dvd_iff z).2 h
      exact ⟨w, by rw [hz, hw, pow_succ]; ring⟩
    · intro h
      have hS := S_eq_of_dvd h
      obtain ⟨z, hz⟩ := h
      have hx : x = y + 2 ^ (k + 1) * z := by rw [← hz]; ring
      rw [Q_partial x (k + 1), Q_partial y (k + 1), hS, add_sub_add_left_eq_sub, ← mul_sub]
      exact dvd_mul_right _ _

lemma norm_le_iff_dvd (a : ℤ_[2]) (k : ℕ) :
    ‖a‖ ≤ (2 : ℝ) ^ (-(k : ℤ)) ↔ (2 : ℤ_[2]) ^ k ∣ a := by
  have := norm_le_pow_iff_mem_span_pow a k
  rw [Ideal.mem_span_singleton] at this
  exact_mod_cast this

lemma eq_zero_of_forall_dvd {b : ℤ_[2]} (h : ∀ k : ℕ, (2 : ℤ_[2]) ^ k ∣ b) : b = 0 := by
  by_contra hb
  have h1 := (norm_le_iff_dvd b (b.valuation + 1)).2 (h _)
  rw [norm_eq_zpow_neg_valuation hb] at h1
  push_cast at h1
  rw [zpow_le_zpow_iff_right₀ (by norm_num)] at h1
  omega

/-- Two 2-adic integers with the same divisibility by every power of `2` have equal norms. -/
lemma norm_eq_of_dvd_iff {a b : ℤ_[2]} (h : ∀ k : ℕ, (2 : ℤ_[2]) ^ k ∣ a ↔ (2 : ℤ_[2]) ^ k ∣ b) :
    ‖a‖ = ‖b‖ := by
  have key : ∀ {a b : ℤ_[2]}, (∀ k : ℕ, (2 : ℤ_[2]) ^ k ∣ a ↔ (2 : ℤ_[2]) ^ k ∣ b) →
      a ≠ 0 → ‖b‖ ≤ ‖a‖ := by
    intro a b h ha
    rw [norm_eq_zpow_neg_valuation ha]
    have h1 := (norm_le_iff_dvd b a.valuation).2
      ((h _).1 ((norm_le_iff_dvd a _).1 (by rw [norm_eq_zpow_neg_valuation ha]; norm_num)))
    push_cast at h1 ⊢
    exact h1
  by_cases ha : a = 0
  · have hb : b = 0 := eq_zero_of_forall_dvd (fun k => (h k).1 (by rw [ha]; exact dvd_zero _))
    rw [ha, hb]
  by_cases hb : b = 0
  · exact absurd (eq_zero_of_forall_dvd (fun k => (h k).2 (by rw [hb]; exact dvd_zero _))) ha
  exact le_antisymm (key (fun k => (h k).symm) hb) (key h ha)

theorem Q_isometry : Isometry Q := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_eq_of_dvd_iff (fun k => pow_dvd_Q_sub_iff k x y)

/-! ## `Q` is onto -/

theorem Q_surjective : Function.Surjective Q := by
  intro y
  have hclosed : IsClosed (Set.range Q) :=
    (Q_isometry.isUniformInducing.isComplete_range).isClosed
  suffices y ∈ closure (Set.range Q) by rwa [hclosed.closure_eq] at this
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_neg_lt 2 hε
  -- pick `n < 2^k` with `parityVec k n = appr y k`
  have hlt : y.appr k < 2 ^ k := appr_lt y k
  obtain ⟨n, hn⟩ := (parityVec_bijective k).2 ⟨y.appr k, hlt⟩
  have hn' : parityVec k n = y.appr k := congrArg Fin.val hn
  refine ⟨Q (n : ℕ), ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hk
  push_cast
  rw [norm_le_iff_dvd]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (appr_spec k y)
  rw [Q_partial _ k, S_natCast, hn']
  exact ⟨w - Q (T^[k] ((n : ℕ) : ℤ_[2])), by push_cast at hw ⊢; rw [mul_sub, ← hw]; ring⟩

theorem Q_bijective : Function.Bijective Q := ⟨Q_isometry.injective, Q_surjective⟩

/-- **Lagarias' theorem**: `Q` is an isometric bijection of `ℤ₂` conjugating `T` to the shift. -/
noncomputable def Qequiv : ℤ_[2] ≃ᵢ ℤ_[2] :=
  IsometryEquiv.mk (Equiv.ofBijective Q Q_bijective) Q_isometry

theorem Qequiv_conj (x : ℤ_[2]) : Qequiv (T x) = shift (Qequiv x) := Q_conj x

end Collatz.TwoAdic
