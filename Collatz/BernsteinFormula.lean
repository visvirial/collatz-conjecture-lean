import Collatz.Bernoulli
import Collatz.Bernstein

/-!
# Bernstein's explicit formula for the inverse conjugacy map

Reference: D. J. Bernstein, *A non-iterative 2-adic statement of the 3N+1 conjecture*,
Proc. Amer. Math. Soc. **121** (1994), 405–408; see also D. J. Bernstein and J. C. Lagarias,
*The 3x+1 conjugacy map*, Canad. J. Math. **48** (1996), 1154–1169.

Let `Q : ℤ₂ → ℤ₂` be Lagarias' conjugacy map (`Collatz.TwoAdic.Q`, with inverse
`Φ = Qequiv.symm`). Bernstein found a closed, non-iterative formula for `Φ`: if
`y = 2^{d_0} + 2^{d_1} + ⋯` with `d_0 < d_1 < ⋯`, then

  `Φ y = - ∑_i 2^{d_i} / 3^{i+1}`.

In terms of the binary digits `b_i = bits y i`, the `i`-th term is present iff `b_i = 1`, and
then the exponent of `3` is `1 + #{l < i | b_l = 1}`. Here `1/3` is the 2-adic unit
`Ring.inverse 3`.

Main results:
* `bernstein_formula`: for every `y : ℤ_[2]`,
  `Φ y = - ∑' i, bv (bits y i) * 2^i * (3⁻¹)^(1 + #{l < i | bits y l})`.
* `bernstein_formula_finite`: for `d_0 < ⋯ < d_{r-1}`,
  `3^r * Φ (∑ 2^{d_i}) = - ∑_{i<r} 3^{r-1-i} 2^{d_i}`.
* `conjecture_iff_bernstein`: Bernstein's form of the conjecture,
  `Conjecture ↔ ∀ n ≥ 1, ∃ m : ℤ, n = Φ (m / 3)`, i.e. `ℤ⁺ ⊆ Φ((1/3) ℤ)`.

Proof: for a bit sequence `b`, let `B b` be the right-hand side. Splitting off the first term
gives `B b = 2 B b'` if `b_0 = 0` and `3 B b + 1 = 2 B b'` if `b_0 = 1`, where `b'` is the
shifted sequence. Hence `B b` has parity `b_0` and `T (B b) = B b'`, so `Q (B b)` and
`ofBits b` satisfy the same digit recursion; their difference is divisible by every power
of `2`, so `Q (B b) = ofBits b`.
-/

namespace Collatz.TwoAdic

open PadicInt Finset

/-! ## The unit `1/3` -/

lemma isUnit_three : IsUnit (3 : ℤ_[2]) := by
  by_contra hu
  have hm : (3 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).2 hu
  rw [← ker_toZMod, RingHom.mem_ker, show (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) by norm_num,
    map_natCast] at hm
  exact absurd hm (by decide)

lemma three_mul_inv_three : (3 : ℤ_[2]) * Ring.inverse 3 = 1 :=
  Ring.mul_inverse_cancel _ isUnit_three

/-! ## Bernstein's series -/

/-- The number of `1` bits among `b 0, …, b (i-1)`. -/
def onesBefore (b : ℕ → Bool) (i : ℕ) : ℕ := ((range i).filter (fun l => b l = true)).card

lemma onesBefore_succ (b : ℕ → Bool) (i : ℕ) :
    onesBefore b (i + 1) = (if b 0 = true then 1 else 0) + onesBefore (fun l => b (l + 1)) i := by
  simp only [onesBefore, card_filter]
  rw [sum_range_succ', add_comm]

/-- The `i`-th term of Bernstein's series: `b_i 2^i / 3^(1 + #{l < i | b_l})`. -/
noncomputable def bTerm (b : ℕ → Bool) (i : ℕ) : ℤ_[2] :=
  bv (b i) * 2 ^ i * Ring.inverse (3 : ℤ_[2]) ^ (1 + onesBefore b i)

lemma summable_bTerm (b : ℕ → Bool) : Summable (bTerm b) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [bTerm, norm_mul, norm_mul, norm_pow, norm_pow,
    show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, norm_p]
  have h1 := norm_bv_le (b i)
  have h2 : ‖Ring.inverse (3 : ℤ_[2])‖ ^ (1 + onesBefore b i) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_le_one _)
  have h3 : (0 : ℝ) ≤ ((2 : ℕ) : ℝ)⁻¹ ^ i := by positivity
  calc ‖bv (b i)‖ * ((2 : ℕ) : ℝ)⁻¹ ^ i * ‖Ring.inverse (3 : ℤ_[2])‖ ^ (1 + onesBefore b i)
        ≤ 1 * ((2 : ℕ) : ℝ)⁻¹ ^ i * 1 := by gcongr
    _ = (1 / 2) ^ i := by norm_num

/-- Bernstein's series `B b = - ∑ b_i 2^i / 3^(1 + #{l < i | b_l})`. -/
noncomputable def bern (b : ℕ → Bool) : ℤ_[2] := -∑' i, bTerm b i

lemma bTerm_zero (b : ℕ → Bool) : bTerm b 0 = bv (b 0) * Ring.inverse 3 := by
  simp [bTerm, onesBefore]

lemma bTerm_succ (b : ℕ → Bool) (i : ℕ) :
    bTerm b (i + 1) =
      2 * (if b 0 = true then Ring.inverse 3 else 1) * bTerm (fun l => b (l + 1)) i := by
  rw [bTerm, bTerm, onesBefore_succ]
  rcases b 0 with _ | _
  · simp only [Bool.false_eq_true, ite_false, zero_add]; ring
  · simp only [ite_true]; ring

lemma bern_rec (b : ℕ → Bool) :
    bern b = -(bv (b 0) * Ring.inverse 3) +
      2 * (if b 0 = true then Ring.inverse 3 else 1) * bern (fun l => b (l + 1)) := by
  rw [bern, bern, (summable_bTerm b).tsum_eq_zero_add]
  simp_rw [bTerm_succ]
  rw [(summable_bTerm (fun l => b (l + 1))).tsum_mul_left, bTerm_zero]
  ring

lemma bern_of_false {b : ℕ → Bool} (h : b 0 = false) :
    bern b = 2 * bern (fun l => b (l + 1)) := by
  rw [bern_rec, h]; simp [bv]

lemma bern_of_true {b : ℕ → Bool} (h : b 0 = true) :
    3 * bern b + 1 = 2 * bern (fun l => b (l + 1)) := by
  have hr := bern_rec b
  rw [h] at hr
  simp only [bv, ite_true, one_mul] at hr
  linear_combination 3 * hr + (2 * bern (fun l => b (l + 1)) - 1) * three_mul_inv_three

lemma par_bern (b : ℕ → Bool) : par (bern b) = if b 0 = true then 1 else 0 := by
  rcases h : b 0 with _ | _
  · rw [bern_of_false h, show 2 * bern (fun l => b (l + 1)) = 0 + 2 * bern (fun l => b (l + 1))
      by ring, par_add_two_mul, par_zero]
    simp
  · have e : bern b = -1 + 2 * (bern (fun l => b (l + 1)) - bern b) := by
      linear_combination bern_of_true h
    rw [e, par_add_two_mul, par_neg_one]
    simp

lemma T_bern (b : ℕ → Bool) : T (bern b) = bern (fun l => b (l + 1)) := by
  unfold T
  apply half_eq
  rw [par_bern]
  rcases h : b 0 with _ | _
  · simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, add_zero]
    exact (bern_of_false h).symm
  · simp only [ite_true, Nat.cast_one, one_mul]
    linear_combination (-1 : ℤ_[2]) * bern_of_true h

lemma Q_bern_sub_dvd : ∀ (k : ℕ) (b : ℕ → Bool), (2 : ℤ_[2]) ^ k ∣ Q (bern b) - ofBits b
  | 0, _ => by simp
  | k + 1, b => by
    obtain ⟨z, hz⟩ := Q_bern_sub_dvd k (fun l => b (l + 1))
    have e : Q (bern b) - ofBits b =
        2 * (Q (bern (fun l => b (l + 1))) - ofBits (fun l => b (l + 1))) := by
      rw [Q_rec, T_bern, par_bern, ofBits_rec]
      rcases b 0 with _ | _ <;> simp [bv] <;> ring
    exact ⟨z, by rw [e, hz]; ring⟩

/-- `Q` maps Bernstein's series for `b` to the 2-adic integer with digits `b`. -/
theorem Q_bern (b : ℕ → Bool) : Q (bern b) = ofBits b :=
  sub_eq_zero.1 (eq_zero_of_forall_dvd (fun k => Q_bern_sub_dvd k b))

theorem Qequiv_symm_ofBits (b : ℕ → Bool) : Qequiv.symm (ofBits b) = bern b := by
  have h : Qequiv (bern b) = ofBits b := Q_bern b
  rw [← h, Qequiv.symm_apply_apply]

/-! ## Bernstein's formula -/

/-- **Bernstein's formula** (1994): writing `y = ∑ b_i 2^i`, the inverse conjugacy map is
`Φ y = - ∑ b_i 2^i / 3^(1 + #{l < i | b_l = 1})`; equivalently, for
`y = 2^{d_0} + 2^{d_1} + ⋯` with `d_0 < d_1 < ⋯`, `Φ y = - ∑_i 2^{d_i} / 3^{i+1}`. -/
theorem bernstein_formula (y : ℤ_[2]) :
    Qequiv.symm y = -∑' i, bv (bits y i) * 2 ^ i *
      Ring.inverse (3 : ℤ_[2]) ^ (1 + ((range i).filter (fun l => bits y l = true)).card) := by
  conv_lhs => rw [← ofBits_bits y]
  rw [Qequiv_symm_ofBits]
  rfl

/-- A sum over `ℕ` supported on the range of an injective `d : Fin r → ℕ`. -/
lemma tsum_eq_sum_fin {r : ℕ} {d : Fin r → ℕ} (hd : Function.Injective d) (f : ℕ → ℤ_[2])
    (hf : ∀ l, (∀ k, d k ≠ l) → f l = 0) : ∑' l, f l = ∑ j, f (d j) := by
  rw [tsum_eq_sum (s := univ.image d) (fun l hl => hf l (fun k hk => hl (by simp [← hk])))]
  exact sum_image (fun x _ y _ h => hd h)

/-- **Bernstein's formula, finite form**: if `d_0 < ⋯ < d_{r-1}`, then
`3^r Φ(2^{d_0} + ⋯ + 2^{d_{r-1}}) = -(3^{r-1} 2^{d_0} + 3^{r-2} 2^{d_1} + ⋯ + 2^{d_{r-1}})`. -/
theorem bernstein_formula_finite {r : ℕ} (d : Fin r → ℕ) (hd : StrictMono d) :
    (3 : ℤ_[2]) ^ r * Qequiv.symm (∑ i, (2 : ℤ_[2]) ^ d i) =
      -∑ i : Fin r, (3 : ℤ_[2]) ^ (r - 1 - i) * 2 ^ d i := by
  set b : ℕ → Bool := fun l => decide (∃ k, d k = l) with hbdef
  have hbd : ∀ j, b (d j) = true := fun j => by simp [hbdef]
  have hb0 : ∀ l, (∀ k, d k ≠ l) → b l = false := fun l hl => by simp [hbdef, hl]
  have hy : ofBits b = ∑ j, (2 : ℤ_[2]) ^ d j := by
    rw [ofBits, tsum_eq_sum_fin hd.injective _ (fun l hl => by simp [hb0 l hl, bv])]
    simp [hbd, bv]
  have hcnt : ∀ j, onesBefore b (d j) = j := by
    intro j
    have e : (range (d j)).filter (fun l => b l = true) = (Iio j).image d := by
      ext l
      simp only [mem_filter, mem_range, mem_image, mem_Iio, hbdef, decide_eq_true_eq]
      constructor
      · rintro ⟨hl, k, rfl⟩; exact ⟨k, hd.lt_iff_lt.1 hl, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨hd hk, k, rfl⟩
    rw [onesBefore, e, card_image_of_injective _ hd.injective, Fin.card_Iio]
  rw [← hy, Qequiv_symm_ofBits, bern,
    tsum_eq_sum_fin hd.injective _ (fun l hl => by simp [bTerm, hb0 l hl, bv]), mul_neg,
    mul_sum]
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  rw [bTerm, hbd, hcnt]
  have hj := j.isLt
  have h3 : (3 : ℤ_[2]) ^ r = 3 ^ (r - 1 - j) * 3 ^ (1 + (j : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (3 : ℤ_[2]) ^ (1 + (j : ℕ)) * Ring.inverse 3 ^ (1 + (j : ℕ)) = 1 := by
    rw [← mul_pow, three_mul_inv_three, one_pow]
  rw [h3]
  simp only [bv, ite_true, one_mul]
  linear_combination (3 ^ (r - 1 - (j : ℕ)) * 2 ^ d j : ℤ_[2]) * h1

/-! ## Bernstein's form of the conjecture -/

/-- For `n ≥ 1`: `n` reaches `1` iff `n = Φ(m/3)` for some integer `m`. -/
theorem reachesOne_iff_bernstein {n : ℕ} (hn : 1 ≤ n) :
    ReachesOne n ↔ ∃ m : ℤ, (n : ℤ_[2]) = Qequiv.symm (m * Ring.inverse 3) := by
  rw [reachesOne_iff_three_mul_Q hn]
  refine exists_congr fun m => ⟨fun h => ?_, fun h => ?_⟩
  · have e : Qequiv (n : ℤ_[2]) = m * Ring.inverse 3 := by
      change Q (n : ℤ_[2]) = _
      linear_combination Ring.inverse (3 : ℤ_[2]) * h - Q (n : ℤ_[2]) * three_mul_inv_three
    rw [← e, Qequiv.symm_apply_apply]
  · have e : Q (n : ℤ_[2]) = m * Ring.inverse 3 := by
      have := congrArg Qequiv h
      rwa [Qequiv.apply_symm_apply] at this
    linear_combination 3 * e + (m : ℤ_[2]) * three_mul_inv_three

/-- **Bernstein's non-iterative 2-adic form of the Collatz conjecture** (1994): the conjecture
holds iff every positive integer lies in `Φ((1/3) ℤ)`, where `Φ = Q⁻¹`. -/
theorem conjecture_iff_bernstein :
    Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, (n : ℤ_[2]) = Qequiv.symm (m * Ring.inverse 3) :=
  forall₂_congr fun _ hn => reachesOne_iff_bernstein hn

end Collatz.TwoAdic

/-! ## Axioms -/

/--
info: 'Collatz.TwoAdic.bernstein_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.TwoAdic.bernstein_formula

/--
info: 'Collatz.TwoAdic.bernstein_formula_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.TwoAdic.bernstein_formula_finite

/--
info: 'Collatz.TwoAdic.conjecture_iff_bernstein' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.TwoAdic.conjecture_iff_bernstein
