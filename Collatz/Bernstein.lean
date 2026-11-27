import Collatz.Periodic

/-!
# The 2-adic integrality form of the Collatz conjecture

The Collatz conjecture is equivalent to an integrality statement about the conjugacy map `Q`
(Lagarias 1985, §2.8, "third form"; Bernstein 1994 restated it via an explicit formula for
`Q⁻¹`, which is not formalized here): a positive integer `n` reaches `1` if and only if `3 Q(n)` is an
ordinary integer, i.e. `Q(n) ∈ ℤ[1/3] ∩ ℤ₂ = (1/3) ℤ`.

* `three_mul_Q_one`: `3 Q(1) = -1`, i.e. `Q(1) = -1/3 = …010101₂` (the parity sequence of the
  trivial cycle `1 → 2 → 1`); also `3 Q(2) = -2`.
* `reachesOne_iff_exists_kstepT`: reaching `1` under `step` or under `kstepT` is the same.
* `reachesOne_iff_three_mul_Q`: for `n ≥ 1`, `ReachesOne n ↔ ∃ z : ℤ, 3 Q(n) = z`.
* `conjecture_iff_three_mul_Q`: the Collatz conjecture holds iff `3 Q(n) ∈ ℤ` for all `n ≥ 1`.

Proof of the converse: if `3 Q(n) = z ∈ ℤ`, then `3 Q(T^m n) = w_m ∈ ℤ` for every `m`
(peel off one digit at a time with `Q_rec`), and `z = 3 Q_m(n) + 2^m w_m` with
`0 ≤ Q_m(n) < 2^m`. Taking `2^m > |z|` forces `w_m ∈ {-3, -2, -1, 0}`, i.e.
`Q(T^m n) ∈ {Q(-1), Q(2), Q(1), Q(0)}`; by injectivity of `Q` the positive integer `T^m n`
is `2` or `1`.
-/

namespace Collatz.TwoAdic

open PadicInt Finset

/-! ## Reaching `1` with the accelerated map -/

lemma exists_kstepT_of_step_iterate : ∀ k n : ℕ, step^[k] n = 1 → ∃ j, kstepT^[j] n = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n h
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    obtain _ | k := k
    · exact absurd h h1
    rw [Function.iterate_succ_apply] at h
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · rw [step_even he] at h
      obtain ⟨j, hj⟩ := ih k (by omega) _ h
      exact ⟨j + 1, by rw [Function.iterate_succ_apply, kstepT_of_even he]; exact hj⟩
    · rw [step_odd ho] at h
      obtain _ | k := k
      · simp at h; omega
      rw [Function.iterate_succ_apply, step_even (by omega)] at h
      obtain ⟨j, hj⟩ := ih k (by omega) _ h
      exact ⟨j + 1, by rw [Function.iterate_succ_apply, kstepT_of_odd ho]; exact hj⟩

lemma reachesOne_of_kstepT_iterate : ∀ (j n : ℕ), kstepT^[j] n = 1 → ReachesOne n
  | 0, _, h => ⟨0, h⟩
  | j + 1, n, h => by
    rw [Function.iterate_succ_apply] at h
    obtain ⟨k, hk⟩ := reachesOne_of_kstepT_iterate j _ h
    obtain ⟨i, -, hi⟩ := kstepT_iter n
    exact ⟨k + i, by rw [Function.iterate_add_apply, hi, hk]⟩

/-- Reaching `1` under `step` is the same as reaching `1` under the accelerated map `kstepT`. -/
theorem reachesOne_iff_exists_kstepT (n : ℕ) : ReachesOne n ↔ ∃ j, kstepT^[j] n = 1 :=
  ⟨fun ⟨k, hk⟩ => exists_kstepT_of_step_iterate k n hk,
    fun ⟨j, hj⟩ => reachesOne_of_kstepT_iterate j n hj⟩

lemma one_le_kstepT {x : ℕ} (hx : 1 ≤ x) : 1 ≤ kstepT x := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [kstepT_of_even h]; omega
  · rw [kstepT_of_odd h]; omega

lemma one_le_kstepT_iterate {x : ℕ} (hx : 1 ≤ x) : ∀ m, 1 ≤ kstepT^[m] x
  | 0 => hx
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    exact one_le_kstepT (one_le_kstepT_iterate hx m)

/-! ## Values of `Q` at a few points -/

lemma three_ne_zero' : (3 : ℤ_[2]) ≠ 0 := by norm_num

lemma par_zero : par (0 : ℤ_[2]) = 0 := by simpa using par_natCast 0

lemma par_one : par (1 : ℤ_[2]) = 1 := by simpa using par_natCast 1

lemma par_two : par (2 : ℤ_[2]) = 0 := by simpa using par_natCast 2

lemma par_neg_one : par (-1 : ℤ_[2]) = 1 := by
  rw [par, map_neg, map_one]; rfl

lemma T_zero : T (0 : ℤ_[2]) = 0 := by
  have := T_natCast 0
  rw [show kstepT 0 = 0 from rfl] at this
  exact_mod_cast this

lemma T_one : T (1 : ℤ_[2]) = 2 := by
  have := T_natCast 1
  rw [show kstepT 1 = 2 from rfl] at this
  exact_mod_cast this

lemma T_two : T (2 : ℤ_[2]) = 1 := by
  have := T_natCast 2
  rw [show kstepT 2 = 1 from rfl] at this
  exact_mod_cast this

lemma T_neg_one : T (-1 : ℤ_[2]) = -1 := by
  apply half_eq
  rw [par_neg_one]; push_cast; ring

lemma Q_zero : Q (0 : ℤ_[2]) = 0 := by
  have h := Q_rec 0
  rw [par_zero, T_zero] at h
  push_cast at h
  linear_combination -h

lemma Q_neg_one : Q (-1 : ℤ_[2]) = -1 := by
  have h := Q_rec (-1)
  rw [par_neg_one, T_neg_one] at h
  push_cast at h
  linear_combination -h

/-- `Q(1) = -1/3 = …010101₂`: the parity sequence `1, 0, 1, 0, …` of the cycle `1 → 2 → 1`. -/
theorem three_mul_Q_one : 3 * Q (1 : ℤ_[2]) = -1 := by
  have h1 := Q_rec 1
  rw [par_one, T_one] at h1
  have h2 := Q_rec 2
  rw [par_two, T_two] at h2
  push_cast at h1 h2
  linear_combination -h1 - 2 * h2

theorem Q_two : Q (2 : ℤ_[2]) = 2 * Q 1 := by
  have h2 := Q_rec 2
  rw [par_two, T_two] at h2
  push_cast at h2
  linear_combination h2

/-- `Q(2) = -2/3 = …101010₂`. -/
theorem three_mul_Q_two : 3 * Q (2 : ℤ_[2]) = -2 := by
  rw [Q_two]; linear_combination 2 * three_mul_Q_one

/-! ## The integrality criterion -/

/-- If `3 Q(x)` is an integer, so is `3 Q(T^m x)` for every `m`. -/
lemma three_mul_Q_iterate_int {x : ℤ_[2]} {z : ℤ} (h : 3 * Q x = z) :
    ∀ m, ∃ w : ℤ, 3 * Q (T^[m] x) = w
  | 0 => ⟨z, h⟩
  | m + 1 => by
    obtain ⟨w, hw⟩ := three_mul_Q_iterate_int h m
    have hr := Q_rec (T^[m] x)
    have e : ((w - 3 * (par (T^[m] x) : ℤ) : ℤ) : ℤ_[2]) = 2 * (3 * Q (T^[m + 1] x)) := by
      rw [Function.iterate_succ_apply']
      push_cast
      rw [← hw, hr]
      ring
    have h2 : (2 : ℤ) ∣ w - 3 * (par (T^[m] x) : ℤ) := by
      have := congrArg toZMod e
      rw [map_intCast, map_mul, toZMod_two, zero_mul] at this
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 this
    obtain ⟨v, hv⟩ := h2
    refine ⟨v, ?_⟩
    rw [hv] at e
    push_cast at e
    exact mul_left_cancel₀ two_ne_zero e.symm

theorem exists_kstepT_of_three_mul_Q {n : ℕ} (hn : 1 ≤ n) {z : ℤ}
    (h : 3 * Q (n : ℤ_[2]) = z) : ∃ j, kstepT^[j] n = 1 := by
  obtain ⟨w, hw⟩ := three_mul_Q_iterate_int h z.natAbs
  have hpart := Q_partial (n : ℤ_[2]) z.natAbs
  rw [S_natCast] at hpart
  have hz : z = 3 * (parityVec z.natAbs n : ℤ) + 2 ^ z.natAbs * w := by
    have : ((z : ℤ) : ℤ_[2]) = ((3 * (parityVec z.natAbs n : ℤ) + 2 ^ z.natAbs * w : ℤ) : ℤ_[2]) := by
      push_cast
      rw [← h, ← hw, hpart]
      ring
    exact Int.cast_injective this
  have hlt : (parityVec z.natAbs n : ℤ) < 2 ^ z.natAbs := by
    exact_mod_cast parityVec_lt n z.natAbs
  have hm : (z.natAbs : ℤ) < 2 ^ z.natAbs := by
    exact_mod_cast (Nat.lt_two_pow_self (n := z.natAbs))
  rw [Int.natCast_natAbs] at hm
  obtain ⟨hz1, hz2⟩ := abs_lt.1 hm
  have hP : (0 : ℤ) ≤ parityVec z.natAbs n := by positivity
  have hN : (0 : ℤ) < 2 ^ z.natAbs := by positivity
  have hw1 : w < 1 := by
    by_contra hc
    have := not_lt.1 hc
    nlinarith
  have hw2 : -4 < w := by
    by_contra hc
    have := not_lt.1 hc
    nlinarith
  rw [T_iterate_natCast] at hw
  have hk := one_le_kstepT_iterate hn z.natAbs
  have key : ∀ y, 3 * Q y = (w : ℤ_[2]) → ((kstepT^[z.natAbs] n : ℕ) : ℤ_[2]) = y :=
    fun y hy => Q_isometry.injective (mul_left_cancel₀ three_ne_zero' (hw.trans hy.symm))
  have hcases : w = -3 ∨ w = -2 ∨ w = -1 ∨ w = 0 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have e := key (-1) (by rw [Q_neg_one]; push_cast; ring)
    have e' : ((kstepT^[z.natAbs] n + 1 : ℕ) : ℤ_[2]) = 0 := by push_cast; rw [e]; ring
    exact absurd (Nat.cast_eq_zero.1 e') (by omega)
  · have e := key 2 (by rw [three_mul_Q_two]; push_cast; ring)
    have e' : kstepT^[z.natAbs] n = 2 := by exact_mod_cast e
    exact ⟨z.natAbs + 1, by rw [Function.iterate_succ_apply', e']; rfl⟩
  · have e := key 1 (by rw [three_mul_Q_one]; push_cast; ring)
    have e' : kstepT^[z.natAbs] n = 1 := by exact_mod_cast e
    exact ⟨z.natAbs, e'⟩
  · have e := key 0 (by rw [Q_zero]; push_cast; ring)
    have e' : kstepT^[z.natAbs] n = 0 := by exact_mod_cast e
    omega

/-- **Integrality criterion** (Lagarias' third form): a positive integer `n` reaches `1` iff `3 Q(n)` is an integer,
i.e. iff the parity sequence of `n`, read as a 2-adic integer, lies in `(1/3) ℤ`. -/
theorem reachesOne_iff_three_mul_Q {n : ℕ} (hn : 1 ≤ n) :
    ReachesOne n ↔ ∃ z : ℤ, (3 : ℤ_[2]) * Q (n : ℤ_[2]) = z := by
  rw [reachesOne_iff_exists_kstepT]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨3 * (parityVec m n : ℤ) - 2 ^ m, ?_⟩
    rw [Q_partial _ m, S_natCast, T_iterate_natCast, hm]
    push_cast
    linear_combination 2 ^ m * three_mul_Q_one
  · rintro ⟨z, hz⟩
    exact exists_kstepT_of_three_mul_Q hn hz

/-- **2-adic integrality form of the Collatz conjecture** (Lagarias 1985; Bernstein 1994): it holds iff `3 Q(n) ∈ ℤ` for every
positive integer `n`. -/
theorem conjecture_iff_three_mul_Q :
    Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, (3 : ℤ_[2]) * Q (n : ℤ_[2]) = z :=
  forall₂_congr fun _ hn => reachesOne_iff_three_mul_Q hn

end Collatz.TwoAdic
