import Collatz.TwoAdic

/-!
# Periodic points of the 2-adic 3x+1 map

* `card_periodic`: for `p ≥ 1` there are exactly `2^p` points `x ∈ ℤ₂` with `T^p x = x`.
  Via the conjugacy `Q`, they correspond to the periodic points of the shift, which are the
  `a / (1 - 2^p)` with `0 ≤ a < 2^p`.
* `periodic_rational`: every such point is a rational number with odd denominator:
  `(2^p - 3^s) x = c` for some natural `c`, where `s` is the number of odd steps.

In particular every positive integer `n` with `kstepT^[p] n = n` is one of these `2^p`
rational points (see `Collatz.NatCycles`).
-/

namespace Collatz.TwoAdic

open PadicInt Finset

/-! ## The shift -/

lemma toZMod_two : toZMod (2 : ℤ_[2]) = 0 := by simpa using toZMod_two_mul 1

lemma two_mul_shift (y : ℤ_[2]) : 2 * shift y = y - par y :=
  two_mul_half (by rw [two_dvd_iff, map_sub, toZMod_par, sub_self])

lemma eq_par_add_shift (y : ℤ_[2]) : y = par y + 2 * shift y := by rw [two_mul_shift]; ring

lemma shift_nat_add (a : ℕ) (z : ℤ_[2]) : shift ((a : ℤ_[2]) + 2 * z) = ((a / 2 : ℕ) : ℤ_[2]) + z := by
  apply half_eq
  rw [par_add_two_mul, par_natCast]
  have e : (a : ℤ_[2]) = 2 * ((a / 2 : ℕ) : ℤ_[2]) + ((a % 2 : ℕ) : ℤ_[2]) := by
    exact_mod_cast (Nat.div_add_mod a 2).symm
  rw [e]; ring

lemma shift_iterate_nat_add : ∀ (p a : ℕ), a < 2 ^ p → ∀ z : ℤ_[2],
    shift^[p] ((a : ℤ_[2]) + 2 ^ p * z) = z
  | 0, a, ha, z => by
    have : a = 0 := by simpa using ha
    subst this; simp
  | p + 1, a, ha, z => by
    rw [Function.iterate_succ_apply, pow_succ', mul_assoc, shift_nat_add]
    exact shift_iterate_nat_add p (a / 2) (by rw [pow_succ] at ha; omega) z

lemma eq_nat_add_shift_iterate : ∀ (p : ℕ) (y : ℤ_[2]),
    ∃ a : ℕ, a < 2 ^ p ∧ y = (a : ℤ_[2]) + 2 ^ p * shift^[p] y
  | 0, y => ⟨0, by norm_num, by simp⟩
  | p + 1, y => by
    obtain ⟨a, ha, hy⟩ := eq_nat_add_shift_iterate p (shift y)
    refine ⟨par y + 2 * a, by have := par_lt y; rw [pow_succ]; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    conv_lhs => rw [eq_par_add_shift y, hy]
    push_cast; ring

/-! ## Counting the periodic points of the shift -/

lemma isUnit_one_sub_two_pow {p : ℕ} (hp : 1 ≤ p) : IsUnit ((1 : ℤ_[2]) - 2 ^ p) := by
  by_contra hu
  have hm : (1 : ℤ_[2]) - 2 ^ p ∈ IsLocalRing.maximalIdeal ℤ_[2] :=
    (IsLocalRing.mem_maximalIdeal _).2 hu
  rw [← ker_toZMod, RingHom.mem_ker, map_sub, map_one, map_pow, toZMod_two,
    zero_pow (by omega), sub_zero] at hm
  exact one_ne_zero hm

/-- The periodic point of the shift with first `p` digits `a`: `a / (1 - 2^p)`. -/
noncomputable def perPt (p a : ℕ) : ℤ_[2] := (a : ℤ_[2]) * Ring.inverse ((1 : ℤ_[2]) - 2 ^ p)

lemma perPt_mul {p : ℕ} (hp : 1 ≤ p) (a : ℕ) : perPt p a * ((1 : ℤ_[2]) - 2 ^ p) = a := by
  rw [perPt, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_one_sub_two_pow hp), mul_one]

lemma perPt_fixed {p : ℕ} (hp : 1 ≤ p) {a : ℕ} (ha : a < 2 ^ p) :
    shift^[p] (perPt p a) = perPt p a := by
  have e : perPt p a = (a : ℤ_[2]) + 2 ^ p * perPt p a := by
    have := perPt_mul hp a
    linear_combination this
  conv_lhs => rw [e]
  exact shift_iterate_nat_add p a ha _

theorem shift_periodic_eq_range {p : ℕ} (hp : 1 ≤ p) :
    {y : ℤ_[2] | shift^[p] y = y} = Set.range (fun a : Fin (2 ^ p) => perPt p a) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hy
    obtain ⟨a, ha, he⟩ := eq_nat_add_shift_iterate p y
    rw [hy] at he
    refine ⟨⟨a, ha⟩, ?_⟩
    have hu := isUnit_one_sub_two_pow hp
    have h1 : y * ((1 : ℤ_[2]) - 2 ^ p) = a := by linear_combination he
    have h2 := perPt_mul hp a
    exact (hu.mul_left_inj).1 (h2.trans h1.symm)
  · rintro ⟨a, rfl⟩
    exact perPt_fixed hp a.2

lemma perPt_injective {p : ℕ} (hp : 1 ≤ p) :
    Function.Injective (fun a : Fin (2 ^ p) => perPt p a) := by
  intro a b h
  have h' : ((a : ℕ) : ℤ_[2]) = ((b : ℕ) : ℤ_[2]) := by
    rw [← perPt_mul hp a, ← perPt_mul hp b]
    exact congrArg (· * ((1 : ℤ_[2]) - 2 ^ p)) h
  exact Fin.ext (Nat.cast_injective h')

theorem card_shift_periodic {p : ℕ} (hp : 1 ≤ p) :
    Nat.card {y : ℤ_[2] // shift^[p] y = y} = 2 ^ p := by
  have := Nat.card_range_of_injective (perPt_injective hp)
  rw [← shift_periodic_eq_range hp] at this
  rw [Nat.card_eq_fintype_card (α := Fin (2 ^ p)), Fintype.card_fin] at this
  exact this

/-! ## Periodic points of `T` -/

lemma Q_iterate (p : ℕ) (x : ℤ_[2]) : Q (T^[p] x) = shift^[p] (Q x) :=
  (Function.Semiconj.iterate_right (f := Q) (ga := T) (gb := shift) Q_conj p) x

/-- **There are exactly `2^p` points of period dividing `p` in `ℤ₂`.** -/
theorem card_periodic {p : ℕ} (hp : 1 ≤ p) : Nat.card {x : ℤ_[2] // T^[p] x = x} = 2 ^ p := by
  rw [← card_shift_periodic hp]
  refine Nat.card_congr (Equiv.subtypeEquiv Qequiv.toEquiv (fun x => ?_))
  change T^[p] x = x ↔ shift^[p] (Q x) = Q x
  rw [← Q_iterate, Q_isometry.injective.eq_iff]

lemma iterate_affine_form (x : ℤ_[2]) :
    ∀ j, ∃ c : ℕ, 2 ^ j * T^[j] x = 3 ^ oddCount2 j x * x + c
  | 0 => ⟨0, by simp [oddCount2]⟩
  | j + 1 => by
    obtain ⟨c, hc⟩ := iterate_affine_form x j
    have hp := par_lt (T^[j] x)
    refine ⟨(1 + 2 * par (T^[j] x)) * c + 2 ^ j * par (T^[j] x), ?_⟩
    rw [Function.iterate_succ_apply', oddCount2_succ]
    calc (2 : ℤ_[2]) ^ (j + 1) * T (T^[j] x) = 2 ^ j * (2 * T (T^[j] x)) := by ring
      _ = (1 + 2 * (par (T^[j] x) : ℤ_[2])) * (2 ^ j * T^[j] x) + 2 ^ j * par (T^[j] x) := by
          rw [two_mul_T]; ring
      _ = _ := by
          rw [hc]
          interval_cases h : par (T^[j] x) <;> push_cast <;> ring

/-- **Periodic points are rational with odd denominator**: if `T^p x = x` with `p ≥ 1`,
then `b x = a` for some integers `a, b` with `b` odd. -/
theorem periodic_rational {p : ℕ} (hp : 1 ≤ p) {x : ℤ_[2]} (hx : T^[p] x = x) :
    ∃ a b : ℤ, Odd b ∧ (b : ℤ_[2]) * x = a := by
  obtain ⟨c, hc⟩ := iterate_affine_form x p
  rw [hx] at hc
  refine ⟨c, 2 ^ p - 3 ^ oddCount2 p x, ?_, ?_⟩
  · have h2 : Even ((2 : ℤ) ^ p) := (even_two.pow_of_ne_zero (by omega))
    exact h2.sub_odd (Odd.pow (by decide))
  · push_cast
    linear_combination hc

end Collatz.TwoAdic
