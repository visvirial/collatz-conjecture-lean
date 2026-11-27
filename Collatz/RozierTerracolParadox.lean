import Collatz.Bernstein
import Collatz.StoppingTime
import Collatz.MCycle
import Collatz.Circuit
import Collatz.TerrasD

/-!
# Paradoxical Collatz sequences (Rozier–Terracol)

Reference: O. Rozier, C. Terracol, *Paradoxical behavior in Collatz sequences*,
arXiv:2502.00948 (2025; v4 April 2026).

We work with the accelerated map `T = kstepT` and `q = oddCount j n`, the number of odd
values among `n, T n, …, T^(j-1) n`. A pair `(j, n)` is *paradoxical* if `j ≥ 1`, `n > 2`,
`3^q < 2^j` (so the "expected" ratio `3^q / 2^j` is below `1`) and yet `T^j n ≥ n`.

Main results:

* `lower_bound` (Theorem 2.4, lower bound, integer form):
  `3^q n + (3^q - 2^q) ≤ 2^j T^j n`.
* `upper_bound` (Theorem 2.4, upper bound, integer form):
  `2^j T^j n ≤ 3^q n + 2^(j-q) (3^q - 2^q)`.
* `exists_pow_window` (Lemma 3.1, integer form): for all `N ≥ 1` and `A` there are `a ≥ A`
  and `b` with `3^a < 2^b` and `(4N - 1) 2^b < 4N 3^a`, i.e. `1 - 1/(4N) < 3^a/2^b < 1`.
  It follows from the irrationality of `log 3 / log 2` and Dirichlet's approximation theorem.
* `infinite_paradoxical_of_no_descent` (Theorem 3.2): if `n ≥ 2` and `T^j n ≥ n` for all `j`,
  then there are paradoxical pairs `(j, 2^k n)` with arbitrarily large `oddCount`;
  in particular (`paradoxical_infinite_of_no_descent`) there are infinitely many paradoxical
  pairs.
* `conjecture_of_finite_paradoxical` (Corollary 3.3): if there are only finitely many
  paradoxical pairs, the Collatz conjecture holds.
* `sum_two_pow_mul_iterate_sub` (Lemma 2.5): `4 ∑_{r < 2^j} (2^j T^j r - 3^q r) = j 4^j`.

Nothing is weakened: the inequalities of Theorem 2.4 and Lemma 3.1, and the identity of
Lemma 2.5, are stated over `ℕ` instead of `ℚ`/`ℝ` (equivalent after clearing denominators;
the truncated subtractions are harmless since `2^q ≤ 3^q` and `3^q r ≤ 2^j T^j r`).
All declarations live in the namespace `Collatz.RozierTerracol`.
-/

namespace Collatz

namespace RozierTerracol

/-- `(j, n)` is *paradoxical*: `j ≥ 1`, `n > 2`, `3^q < 2^j` with `q = oddCount j n`, and
still `T^j n ≥ n`. -/
def Paradoxical (j n : ℕ) : Prop :=
  1 ≤ j ∧ 2 < n ∧ 3 ^ oddCount j n < 2 ^ j ∧ n ≤ kstepT^[j] n

/-! ## Theorem 2.4: bounds on `2^j T^j n` -/

/-- Auxiliary form of the lower bound, without truncated subtraction. -/
lemma lower_aux (n : ℕ) :
    ∀ j, 3 ^ oddCount j n * (n + 1) ≤ 2 ^ j * kstepT^[j] n + 2 ^ oddCount j n
  | 0 => by simp [oddCount]
  | j + 1 => by
    have ih := lower_aux n j
    have hq : 2 ^ oddCount j n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (oddCount_le j n)
    rw [Function.iterate_succ_apply', oddCount_succ, pow_succ 2 j]
    generalize kstepT^[j] n = x at ih ⊢
    generalize oddCount j n = q at ih hq ⊢
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [h, Nat.add_zero, kstepT_of_even h]
      have : 2 * (x / 2) = x := by omega
      rw [mul_assoc, this]; exact ih
    · rw [h, kstepT_of_odd h, mul_assoc, show 2 * ((3 * x + 1) / 2) = 3 * x + 1 by omega,
        pow_succ, pow_succ]
      nlinarith

/-- **Theorem 2.4 (lower bound).** With `q = oddCount j n`,
`3^q n + (3^q - 2^q) ≤ 2^j T^j n`. -/
theorem lower_bound (n j : ℕ) :
    3 ^ oddCount j n * n + (3 ^ oddCount j n - 2 ^ oddCount j n) ≤ 2 ^ j * kstepT^[j] n := by
  have h1 := lower_aux n j
  have h2 : 2 ^ oddCount j n ≤ 3 ^ oddCount j n := Nat.pow_le_pow_left (by norm_num) _
  rw [Nat.mul_add, Nat.mul_one] at h1
  generalize 3 ^ oddCount j n = X at *
  generalize 2 ^ oddCount j n = Z at *
  generalize 2 ^ j * kstepT^[j] n = W at *
  generalize X * n = Y at *
  omega

/-- Auxiliary form of the upper bound, without truncated subtraction. -/
lemma upper_aux (n : ℕ) : ∀ j,
    2 ^ j * kstepT^[j] n + 2 ^ j ≤ 3 ^ oddCount j n * n + 2 ^ (j - oddCount j n) * 3 ^ oddCount j n
  | 0 => by simp [oddCount]
  | j + 1 => by
    have ih := upper_aux n j
    have hqj := oddCount_le j n
    have e : 2 ^ j = 2 ^ (j - oddCount j n) * 2 ^ oddCount j n := by
      rw [← pow_add, Nat.sub_add_cancel hqj]
    have hZ : 2 ^ oddCount j n ≤ 3 ^ oddCount j n := Nat.pow_le_pow_left (by norm_num) _
    have hj2 : 2 ^ j ≤ 2 ^ (j - oddCount j n) * 3 ^ oddCount j n := by
      rw [e]; exact Nat.mul_le_mul_left _ hZ
    rw [Function.iterate_succ_apply', oddCount_succ, pow_succ 2 j]
    generalize kstepT^[j] n = x at ih ⊢
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [h, Nat.add_zero, kstepT_of_even h, show j + 1 - oddCount j n = j - oddCount j n + 1 by
        omega, pow_succ]
      have : 2 * (x / 2) = x := by omega
      rw [mul_assoc (2 ^ j), this]
      generalize oddCount j n = q at *
      nlinarith
    · rw [h, kstepT_of_odd h, show j + 1 - (oddCount j n + 1) = j - oddCount j n by omega,
        mul_assoc (2 ^ j), show 2 * ((3 * x + 1) / 2) = 3 * x + 1 by omega, pow_succ]
      generalize oddCount j n = q at *
      nlinarith

/-- **Theorem 2.4 (upper bound).** With `q = oddCount j n`,
`2^j T^j n ≤ 3^q n + 2^(j-q) (3^q - 2^q)`. -/
theorem upper_bound (n j : ℕ) :
    2 ^ j * kstepT^[j] n ≤
      3 ^ oddCount j n * n + 2 ^ (j - oddCount j n) * (3 ^ oddCount j n - 2 ^ oddCount j n) := by
  have h1 := upper_aux n j
  have e : 2 ^ (j - oddCount j n) * 2 ^ oddCount j n = 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel (oddCount_le j n)]
  rw [Nat.mul_sub, e]
  have hj2 : 2 ^ j ≤ 2 ^ (j - oddCount j n) * 3 ^ oddCount j n := by
    rw [← e]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
  omega

/-! ## Lemma 2.5: the average defect over residues -/

/-- The defect `D_j(r) = 2^j T^j r - 3^q r` (nonnegative by `iterate_lower`). -/
def defect (j r : ℕ) : ℕ := 2 ^ j * kstepT^[j] r - 3 ^ oddCount j r * r

lemma defect_succ (j r : ℕ) : defect (j + 1) r =
    if kstepT^[j] r % 2 = 0 then defect j r else 3 * defect j r + 2 ^ j := by
  have hl := iterate_lower r j
  unfold defect
  rw [Function.iterate_succ_apply', oddCount_succ, pow_succ 2 j]
  generalize kstepT^[j] r = x at hl ⊢
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · simp only [h, ite_true]
    rw [Nat.add_zero, kstepT_of_even h, mul_assoc, show 2 * (x / 2) = x by omega]
  · have h' : x % 2 ≠ 0 := by omega
    simp only [h', ite_false]
    rw [h, kstepT_of_odd h, mul_assoc,
      show 2 * ((3 * x + 1) / 2) = 3 * x + 1 by omega, pow_succ,
      show 2 ^ j * (3 * x + 1) = 3 * (2 ^ j * x) + 2 ^ j by ring,
      show 3 ^ oddCount j r * 3 * r = 3 * (3 ^ oddCount j r * r) by ring]
    generalize 2 ^ j * x = W at *
    generalize 3 ^ oddCount j r * r = V at *
    generalize 2 ^ j = P
    omega

lemma defect_affine (j m r : ℕ) : defect j (2 ^ j * m + r) = defect j r := by
  unfold defect
  rw [iterate_affine (k := j) (m := m) (r := r) j le_rfl,
    oddCount_affine (k := j) (m := m) (r := r) j le_rfl, Nat.sub_self, pow_zero, one_mul,
    Nat.mul_add, Nat.mul_add, show 3 ^ oddCount j r * (2 ^ j * m) = 2 ^ j * (3 ^ oddCount j r * m)
      by ring, Nat.add_sub_add_left]

lemma sum_defect (j : ℕ) : 4 * ∑ r ∈ Finset.range (2 ^ j), defect j r = j * 4 ^ j := by
  induction j with
  | zero => simp [defect]
  | succ j ih =>
    have hstep : ∑ r ∈ Finset.range (2 ^ (j + 1)), defect (j + 1) r =
        ∑ r ∈ Finset.range (2 ^ j), (4 * defect j r + 2 ^ j) := by
      rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [defect_succ, defect_succ, iterate_pow_add, show 2 ^ j + r = 2 ^ j * 1 + r by ring,
        defect_affine]
      have h3 := three_pow_mod_two (oddCount j r)
      rcases Nat.mod_two_eq_zero_or_one (kstepT^[j] r) with h | h
      · have h' : (3 ^ oddCount j r + kstepT^[j] r) % 2 ≠ 0 := by omega
        simp only [h, h', ite_true, ite_false]; ring
      · have h' : (3 ^ oddCount j r + kstepT^[j] r) % 2 = 0 := by omega
        have h'' : kstepT^[j] r % 2 ≠ 0 := by omega
        simp only [h', h'', ite_true, ite_false]; ring
    rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    have : 2 ^ j * 2 ^ j = 4 ^ j := by rw [← mul_pow]; norm_num
    rw [this, pow_succ]
    linarith

/-- **Lemma 2.5.** `∑_{r < 2^j} (2^j T^j r - 3^q r) = j 4^(j-1)`, stated as
`4 ∑ … = j 4^j`. -/
theorem sum_two_pow_mul_iterate_sub (j : ℕ) :
    4 * ∑ r ∈ Finset.range (2 ^ j), (2 ^ j * kstepT^[j] r - 3 ^ oddCount j r * r) = j * 4 ^ j :=
  sum_defect j

/-! ## Lemma 3.1: `3^a / 2^b` slightly below `1` -/

/-- `ξ = log 3 / log 2`. -/
noncomputable def xi : ℝ := Real.log 3 / Real.log 2

/-- `a ξ` is never an integer for `a ≥ 1` (since `2^c ≠ 3^a`). -/
lemma int_ne_mul_xi {a : ℕ} (ha : 1 ≤ a) (b : ℤ) : (b : ℝ) ≠ a * xi := by
  intro h
  have hL2 := log_two_pos'
  have hL3 := log_three_pos'
  have h1 : (b : ℝ) * Real.log 2 = a * Real.log 3 := by
    rw [h, xi]; field_simp
  have hb : 0 < b := by
    have h3 : (0 : ℝ) < a * Real.log 3 := mul_pos (by exact_mod_cast ha) hL3
    have : (0 : ℝ) < b := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact_mod_cast this
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = c := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
  have hc : 1 ≤ c := by exact_mod_cast hb
  have h2 : Real.log ((2 : ℝ) ^ c) = Real.log ((3 : ℝ) ^ a) := by
    rw [Real.log_pow, Real.log_pow]; push_cast at h1; linarith
  have h3 : ((2 : ℝ) ^ c) = (3 : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) h2
  have h4 : (2 ^ c : ℕ) = 3 ^ a := by exact_mod_cast h3
  have h5 := three_pow_mod_two a
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [← h4, pow_succ, Nat.mul_mod_left] at h5
  exact absurd h5 (by norm_num)

/-- For every `A` there is a gap `ε ∈ (0, 1]` such that no `b - a ξ` with `a < A` lies in
`(0, ε)`. -/
lemma exists_gap : ∀ A : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
    ∀ a < A, ∀ b : ℤ, ¬ (0 < (b : ℝ) - a * xi ∧ (b : ℝ) - a * xi < ε)
  | 0 => ⟨1, one_pos, le_rfl, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  | A + 1 => by
    obtain ⟨ε, hε, hε1, hA⟩ := exists_gap A
    rcases Nat.eq_zero_or_pos A with rfl | hApos
    · refine ⟨ε, hε, hε1, fun a ha b hb => ?_⟩
      have ha0 : a = 0 := by omega
      subst ha0
      obtain ⟨h1, h2⟩ := hb
      simp only [Nat.cast_zero, zero_mul, sub_zero] at h1 h2
      have h3 : (0 : ℤ) < b := by exact_mod_cast h1
      have h4 : (1 : ℝ) ≤ b := by exact_mod_cast h3
      linarith
    · have hle := Int.le_ceil ((A : ℝ) * xi)
      have hne := int_ne_mul_xi hApos ⌈(A : ℝ) * xi⌉
      have hg : 0 < (⌈(A : ℝ) * xi⌉ : ℝ) - A * xi := sub_pos.2 (lt_of_le_of_ne hle (Ne.symm hne))
      refine ⟨min ε ((⌈(A : ℝ) * xi⌉ : ℝ) - A * xi), lt_min hε hg, (min_le_left _ _).trans hε1,
        fun a ha b hb => ?_⟩
      obtain ⟨h1, h2⟩ := hb
      rcases (show a < A ∨ a = A by omega) with ha | rfl
      · exact hA a ha b ⟨h1, h2.trans_le (min_le_left _ _)⟩
      · have h3 := h2.trans_le (min_le_right _ _)
        have h4 : ⌈(a : ℝ) * xi⌉ ≤ b := Int.ceil_le.2 (by linarith)
        have h5 : ((⌈(a : ℝ) * xi⌉ : ℤ) : ℝ) ≤ b := by exact_mod_cast h4
        linarith

/-- For every `δ > 0` and `A` there are `a ≥ A` and `b` with `0 < b - a ξ < δ`. -/
lemma exists_approx (δ : ℝ) (hδ : 0 < δ) (A : ℕ) :
    ∃ a : ℕ, ∃ b : ℤ, A ≤ a ∧ 0 < (b : ℝ) - a * xi ∧ (b : ℝ) - a * xi < δ := by
  obtain ⟨ε, hε, hε1, hgap⟩ := exists_gap A
  suffices H : ∃ a : ℕ, ∃ b : ℤ, 0 < (b : ℝ) - a * xi ∧ (b : ℝ) - a * xi < min δ ε by
    obtain ⟨a, b, h1, h2⟩ := H
    refine ⟨a, b, ?_, h1, h2.trans_le (min_le_left _ _)⟩
    by_contra hA
    exact hgap a (by omega) b ⟨h1, h2.trans_le (min_le_right _ _)⟩
  have hη : 0 < min δ ε := lt_min hδ hε
  have hη1 : min δ ε ≤ 1 := (min_le_right _ _).trans hε1
  generalize min δ ε = η at hη hη1 ⊢
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le xi hNpos
  have hsmall : 1 / ((N : ℝ) + 1) < η := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hN
    nlinarith
  obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = k' := ⟨k.toNat, (Int.toNat_of_nonneg hk0.le).symm⟩
  have hk' : 1 ≤ k' := by exact_mod_cast hk0
  push_cast at hjk
  have habs := abs_lt.1 (hjk.trans_lt hsmall)
  have hne : (k' : ℝ) * xi - j ≠ 0 := fun h => int_ne_mul_xi hk' j (by linarith)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨k', j, by linarith, by linarith⟩
  · generalize he : (k' : ℝ) * xi - j = e at hpos habs
    have he1 : e < 1 := by linarith [habs.2]
    have hM1 : (⌊1 / e⌋₊ : ℝ) ≤ 1 / e := Nat.floor_le (by positivity)
    have hM2 : 1 / e < ⌊1 / e⌋₊ + 1 := Nat.lt_floor_add_one _
    have hMpos : 1 ≤ ⌊1 / e⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_one, le_div_iff₀ hpos]; linarith
    generalize ⌊1 / e⌋₊ = M at hM1 hM2 hMpos
    have hMe1 : (M : ℝ) * e ≤ 1 := by rwa [le_div_iff₀ hpos] at hM1
    have hMe2 : 1 < ((M : ℝ) + 1) * e := by rwa [div_lt_iff₀ hpos] at hM2
    have hne2 := int_ne_mul_xi (a := M * k') (Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by omega) (by omega))) (M * j + 1)
    have key : ((M * j + 1 : ℤ) : ℝ) - ((M * k' : ℕ) : ℝ) * xi = 1 - M * e := by
      rw [← he]; push_cast; ring
    refine ⟨M * k', M * j + 1, ?_, ?_⟩
    · rw [key]
      rcases (sub_nonneg.2 hMe1).lt_or_eq with h | h
      · exact h
      · exfalso; apply hne2; linarith
    · rw [key]; nlinarith

/-- **Lemma 3.1 (integer form).** For all `N ≥ 1` and `A` there are `a ≥ A` and `b` with
`3^a < 2^b` and `(4N - 1) 2^b < 4N 3^a`. -/
theorem exists_pow_window (N A : ℕ) (hN : 1 ≤ N) :
    ∃ a b, A ≤ a ∧ 3 ^ a < 2 ^ b ∧ (4 * N - 1) * 2 ^ b < 4 * N * 3 ^ a := by
  have hL2 := log_two_pos'
  have hL3 := log_three_pos'
  have hP1 : 4 * N - 1 + 1 = 4 * N := by omega
  have hPpos' : 0 < 4 * N - 1 := by omega
  generalize 4 * N - 1 = P at hP1 hPpos' ⊢
  have hP : (P : ℝ) + 1 = 4 * N := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hPpos'
  have hη : 0 < Real.log (4 * N) - Real.log P :=
    sub_pos.2 (Real.log_lt_log hPpos (by linarith))
  obtain ⟨a, b, hA, h1, h2⟩ :=
    exists_approx ((Real.log (4 * N) - Real.log P) / Real.log 2) (div_pos hη hL2) A
  have e : (b : ℝ) - a * xi = (b * Real.log 2 - a * Real.log 3) / Real.log 2 := by
    rw [xi]; field_simp
  rw [e] at h1 h2
  have h1' : (a : ℝ) * Real.log 3 < b * Real.log 2 := by
    have := (div_pos_iff_of_pos_right hL2).1 h1; linarith
  have h2' : (b : ℝ) * Real.log 2 - a * Real.log 3 < Real.log (4 * N) - Real.log P :=
    (div_lt_div_iff_of_pos_right hL2).1 h2
  have hb : 0 < b := by
    have : (0 : ℝ) < b := by
      by_contra hneg
      push Not at hneg
      have : (0 : ℝ) ≤ a * Real.log 3 := by positivity
      nlinarith
    exact_mod_cast this
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = c := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
  push_cast at h1' h2'
  refine ⟨a, c, hA, ?_, ?_⟩
  · have : Real.log ((3 : ℝ) ^ a) < Real.log ((2 : ℝ) ^ c) := by
      rw [Real.log_pow, Real.log_pow]; exact h1'
    have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 this
    exact_mod_cast this
  · have h4N : (0 : ℝ) < 4 * N := by linarith
    have : Real.log ((P : ℝ) * 2 ^ c) < Real.log ((4 * N : ℝ) * 3 ^ a) := by
      rw [Real.log_mul hPpos.ne' (by positivity), Real.log_mul h4N.ne' (by positivity),
        Real.log_pow, Real.log_pow]
      linarith
    have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 this
    exact_mod_cast this

/-! ## Theorem 3.2: orbits that never descend produce paradoxical pairs -/

lemma oddCount_mono (n : ℕ) {i i' : ℕ} (h : i ≤ i') : oddCount i n ≤ oddCount i' n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [oddCount_succ]; omega

lemma oddCount_add' (m k : ℕ) :
    ∀ j, oddCount (k + j) m = oddCount k m + oddCount j (kstepT^[k] m)
  | 0 => by simp [oddCount]
  | j + 1 => by
    rw [← Nat.add_assoc, oddCount_succ, oddCount_succ, oddCount_add' m k j, Nat.add_comm k j,
      Function.iterate_add_apply]
    omega

lemma two_pow_succ_mul (k n : ℕ) : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring

lemma iterate_two_pow_mul (n : ℕ) : ∀ k, kstepT^[k] (2 ^ k * n) = n
  | 0 => by simp
  | k + 1 => by
    rw [Function.iterate_succ_apply, two_pow_succ_mul, kstepT_of_even (Nat.mul_mod_right 2 _),
      Nat.mul_div_cancel_left _ two_pos, iterate_two_pow_mul n k]

lemma oddCount_two_pow_mul (n : ℕ) : ∀ k, oddCount k (2 ^ k * n) = 0
  | 0 => rfl
  | k + 1 => by
    have h := oddCount_add' (2 ^ (k + 1) * n) 1 k
    rw [Nat.add_comm 1 k] at h
    rw [h, Function.iterate_one, two_pow_succ_mul, kstepT_of_even (Nat.mul_mod_right 2 _),
      Nat.mul_div_cancel_left _ two_pos, oddCount_two_pow_mul n k]
    have : oddCount 1 (2 * (2 ^ k * n)) = 0 + (2 * (2 ^ k * n)) % 2 := rfl
    rw [this, Nat.mul_mod_right]

/-- If the orbit stays positive, `oddCount` is unbounded. -/
lemma oddCount_unbounded {n : ℕ} (hpos : ∀ j, 1 ≤ kstepT^[j] n) : ∀ a, ∃ j, a ≤ oddCount j n
  | 0 => ⟨0, Nat.zero_le _⟩
  | a + 1 => by
    obtain ⟨j, hj⟩ := oddCount_unbounded hpos a
    by_contra hcon
    push Not at hcon
    have heven : ∀ i < kstepT^[j] n, kstepT^[i] (kstepT^[j] n) % 2 = 0 := by
      intro i _
      have h1 := hcon (j + i + 1)
      have h2 := oddCount_mono n (show j ≤ j + i by omega)
      rw [oddCount_succ] at h1
      rw [← Function.iterate_add_apply, Nat.add_comm i j]
      omega
    have h3 := even_run (kstepT^[j] n) heven
    have h4 := hpos (kstepT^[j] n + j)
    rw [Function.iterate_add_apply] at h4
    have h5 : kstepT^[j] n < 2 ^ (kstepT^[j] n) := Nat.lt_two_pow_self
    generalize kstepT^[j] n = y at h3 h4 h5
    generalize kstepT^[y] y = z at h3 h4
    nlinarith

/-- `oddCount` takes every value up to `oddCount j n` (it moves by steps of at most `1`). -/
lemma oddCount_hits (n : ℕ) : ∀ j, ∀ a ≤ oddCount j n, ∃ i, oddCount i n = a
  | 0 => fun a ha => ⟨0, by have : oddCount 0 n = 0 := rfl; omega⟩
  | j + 1 => fun a ha => by
    by_cases h : a ≤ oddCount j n
    · exact oddCount_hits n j a h
    · rw [oddCount_succ] at ha
      refine ⟨j + 1, ?_⟩
      rw [oddCount_succ]
      have := Nat.mod_lt (kstepT^[j] n) two_pos
      omega

/-- **Theorem 3.2.** If `n ≥ 2` and `T^j n ≥ n` for all `j`, then there are paradoxical pairs
`(j, 2^k n)` with arbitrarily large `oddCount`. -/
theorem infinite_paradoxical_of_no_descent {n : ℕ} (hn : 2 ≤ n) (h : ∀ j, n ≤ kstepT^[j] n) :
    ∀ A, ∃ j k, A ≤ oddCount j (2 ^ k * n) ∧ Paradoxical j (2 ^ k * n) := by
  intro A
  have hn3 : 3 ≤ n := by
    by_contra hlt
    obtain rfl : n = 2 := by omega
    exact absurd (h 1) (by decide)
  have hpos : ∀ j, 1 ≤ kstepT^[j] n := fun j => le_trans (by omega) (h j)
  obtain ⟨a, b, hA, hab, hwin⟩ := exists_pow_window n (max A 1) (by omega)
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) hA
  have hAa : A ≤ a := le_trans (le_max_left _ _) hA
  have hlt : a < b := by
    have : 2 ^ a < 2 ^ b := lt_of_le_of_lt (Nat.pow_le_pow_left (by norm_num) a) hab
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  obtain ⟨j0, hj0⟩ := oddCount_unbounded hpos a
  obtain ⟨j, hj⟩ := oddCount_hits n j0 a hj0
  have hja : a ≤ j := hj ▸ oddCount_le j n
  rcases le_or_gt b j with hbj | hjb
  · refine ⟨j, 0, ?_, ?_⟩
    · simpa [hj] using hAa
    · simp only [pow_zero, one_mul]
      refine ⟨by omega, by omega, ?_, h j⟩
      rw [hj]
      exact lt_of_lt_of_le hab (Nat.pow_le_pow_right (by norm_num) hbj)
  · obtain ⟨k, hbk⟩ : ∃ k, b = k + j := ⟨b - j, by omega⟩
    have hT : kstepT^[b] (2 ^ k * n) = kstepT^[j] n := by
      rw [hbk, Nat.add_comm, Function.iterate_add_apply, iterate_two_pow_mul]
    have hq : oddCount b (2 ^ k * n) = a := by
      rw [hbk, oddCount_add', oddCount_two_pow_mul, iterate_two_pow_mul, hj, Nat.zero_add]
    refine ⟨b, k, by omega, ?_⟩
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨by omega, by nlinarith, by rw [hq]; exact hab, ?_⟩
    rw [hT]
    have hlow := lower_bound n j
    rw [hj] at hlow
    have hZ : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
    have hZ2 : 2 * 2 ^ a ≤ 2 ^ b := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hlt
    have hYb : 2 ^ b = 2 ^ j * 2 ^ k := by rw [hbk, pow_add, Nat.mul_comm]
    have hP : 4 * n - 1 + 1 = 4 * n := by omega
    generalize 4 * n - 1 = P at hwin hP
    have key : 2 ^ b * n ≤ 2 ^ j * kstepT^[j] n := by
      have hD : 3 ^ a - 2 ^ a + 2 ^ a = 3 ^ a := Nat.sub_add_cancel hZ
      generalize 3 ^ a - 2 ^ a = D at hlow hD
      generalize 3 ^ a = X at *
      generalize 2 ^ a = Z at *
      generalize 2 ^ j * kstepT^[j] n = W at *
      generalize 2 ^ b = Y at *
      have e : P * Y + Y = 4 * n * Y := by rw [← hP]; ring
      have hwin' : 4 * n * Y < 4 * n * X + Y := by linarith
      have h4X : 3 * Y < 4 * X := by
        by_contra hc
        push Not at hc
        have : n * (4 * X) ≤ n * (3 * Y) := Nat.mul_le_mul_left n hc
        nlinarith
      nlinarith
    rw [hYb, mul_assoc] at key
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- Under the hypotheses of Theorem 3.2 the set of paradoxical pairs is infinite. -/
theorem paradoxical_infinite_of_no_descent {n : ℕ} (hn : 2 ≤ n) (h : ∀ j, n ≤ kstepT^[j] n) :
    {p : ℕ × ℕ | Paradoxical p.1 p.2}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun p : ℕ × ℕ => oddCount p.1 p.2)).bddAbove
  obtain ⟨j, k, hA, hP⟩ := infinite_paradoxical_of_no_descent hn h (M + 1)
  have : oddCount j (2 ^ k * n) ≤ M :=
    hM (Set.mem_image_of_mem _ (show (j, 2 ^ k * n) ∈ {p : ℕ × ℕ | Paradoxical p.1 p.2} from hP))
  omega

/-! ## Corollary 3.3 -/

/-- **Corollary 3.3.** If there are only finitely many paradoxical pairs, then the Collatz
conjecture holds. -/
theorem conjecture_of_finite_paradoxical (h : {p : ℕ × ℕ | Paradoxical p.1 p.2}.Finite) :
    Conjecture := by
  classical
  intro n0 hn0
  by_contra hno
  rw [TwoAdic.reachesOne_iff_exists_kstepT] at hno
  push Not at hno
  have hex : ∃ v, ∃ i, kstepT^[i] n0 = v := ⟨n0, 0, rfl⟩
  obtain ⟨i0, hi0⟩ := Nat.find_spec hex
  have hmin : ∀ i, Nat.find hex ≤ kstepT^[i] n0 := fun i => Nat.find_min' hex ⟨i, rfl⟩
  have horb : ∀ j, Nat.find hex ≤ kstepT^[j] (Nat.find hex) := by
    intro j; have := hmin (j + i0); rwa [Function.iterate_add_apply, hi0] at this
  have hn2 : 2 ≤ Nat.find hex := by
    have h1 := kstepT_iterate_pos hn0 i0
    have h2 := hno i0
    omega
  exact paradoxical_infinite_of_no_descent hn2 horb h

end RozierTerracol

end Collatz

/-- info: 'Collatz.RozierTerracol.conjecture_of_finite_paradoxical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.conjecture_of_finite_paradoxical

/-- info: 'Collatz.RozierTerracol.infinite_paradoxical_of_no_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.infinite_paradoxical_of_no_descent

/-- info: 'Collatz.RozierTerracol.paradoxical_infinite_of_no_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.paradoxical_infinite_of_no_descent

/-- info: 'Collatz.RozierTerracol.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.lower_bound

/-- info: 'Collatz.RozierTerracol.upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.upper_bound

/-- info: 'Collatz.RozierTerracol.exists_pow_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.exists_pow_window

/-- info: 'Collatz.RozierTerracol.sum_two_pow_mul_iterate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.RozierTerracol.sum_two_pow_mul_iterate_sub
