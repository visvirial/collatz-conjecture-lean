import Collatz.Main

/-!
# Constraints on Collatz cycles

Let `n → step n → ⋯ → step^[p] n = n` be a cycle with `a` even steps and `b` odd steps.
Writing `xᵢ = step^[i] n`, the basic multiplicative identity is

  `2^a * ∏_{odd i} xᵢ = ∏_{odd i} (3 xᵢ + 1)`,

from which we get `3^b < 2^a` and, if every odd element is `≥ m`, `m^b * 2^a ≤ (3m+1)^b`.
Combined with the verification of all `n < 1024`, any cycle not containing `1` has at least
41 odd steps, at least 65 even steps, and length at least 106.
-/

namespace Collatz

open Finset

/-- `n` lies on a cycle of length `p` (not necessarily minimal). -/
def IsCycle (n p : ℕ) : Prop := 1 ≤ n ∧ 1 ≤ p ∧ step^[p] n = n

/-- Indices `i < p` where the orbit is even. -/
def evens (n p : ℕ) : Finset ℕ := (range p).filter (fun i => step^[i] n % 2 = 0)

/-- Indices `i < p` where the orbit is odd. -/
def odds (n p : ℕ) : Finset ℕ := (range p).filter (fun i => ¬ step^[i] n % 2 = 0)

lemma card_evens_add_card_odds (n p : ℕ) : (evens n p).card + (odds n p).card = p := by
  rw [evens, odds, card_filter_add_card_filter_not, card_range]

/-- Shifting the orbit by one step does not change a product around a cycle. -/
lemma prod_shift {n p : ℕ} (hp : step^[p] n = n) (f : ℕ → ℕ) :
    ∏ i ∈ range p, f (step^[i + 1] n) = ∏ i ∈ range p, f (step^[i] n) := by
  rcases p with _ | q
  · simp
  · rw [prod_range_succ, prod_range_succ' (fun i => f (step^[i] n)), hp]
    simp

/-- Per-step identity: `c(y) * step y = h(y)`. -/
lemma step_mul (y : ℕ) :
    (if y % 2 = 0 then 2 else 1) * step y = (if y % 2 = 0 then y else 3 * y + 1) := by
  unfold step
  split_ifs <;> omega

/-- **Cycle identity.** `2^a * ∏_{odd} xᵢ = ∏_{odd} (3 xᵢ + 1)`. -/
theorem cycle_identity {n p : ℕ} (hc : IsCycle n p) :
    2 ^ (evens n p).card * ∏ i ∈ odds n p, step^[i] n
      = ∏ i ∈ odds n p, (3 * step^[i] n + 1) := by
  obtain ⟨hn, -, hp⟩ := hc
  set x : ℕ → ℕ := fun i => step^[i] n with hx
  have hpos : ∀ i, 0 < x i := fun i => iterate_pos hn i
  -- product of the per-step identity
  have key : (∏ i ∈ range p, (if x i % 2 = 0 then 2 else 1)) * ∏ i ∈ range p, x (i + 1)
      = ∏ i ∈ range p, (if x i % 2 = 0 then x i else 3 * x i + 1) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp only [hx, Function.iterate_succ_apply']
    exact step_mul _
  have hs : ∏ i ∈ range p, x (i + 1) = ∏ i ∈ range p, x i := prod_shift (f := id) hp
  rw [hs] at key
  -- split products into even and odd parts
  have hc2 : ∏ i ∈ range p, (if x i % 2 = 0 then 2 else 1) = 2 ^ (evens n p).card := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]; rfl
  have hh : ∏ i ∈ range p, (if x i % 2 = 0 then x i else 3 * x i + 1)
      = (∏ i ∈ evens n p, x i) * ∏ i ∈ odds n p, (3 * x i + 1) := by
    rw [prod_ite]; rfl
  have hall : ∏ i ∈ range p, x i = (∏ i ∈ evens n p, x i) * ∏ i ∈ odds n p, x i := by
    rw [evens, odds, prod_filter_mul_prod_filter_not]
  rw [hc2, hh, hall] at key
  have hE : 0 < ∏ i ∈ evens n p, x i := prod_pos fun i _ => hpos i
  apply Nat.eq_of_mul_eq_mul_left hE
  rw [← key]; ring

/-- A cycle has at least one odd step. -/
lemma odds_nonempty {n p : ℕ} (hc : IsCycle n p) : (odds n p).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  have h := cycle_identity hc
  rw [he, prod_empty, prod_empty, mul_one] at h
  have h0 : (evens n p).card = 0 := by
    rcases Nat.eq_zero_or_pos (evens n p).card with h' | h'
    · exact h'
    · have : 2 ≤ 2 ^ (evens n p).card := Nat.le_self_pow (by omega) 2
      omega
  have := card_evens_add_card_odds n p
  rw [he, card_empty] at this
  have := hc.2.1
  omega

/-- **Lower bound.** In a cycle, `3^b < 2^a`. -/
theorem three_pow_lt_two_pow {n p : ℕ} (hc : IsCycle n p) :
    3 ^ (odds n p).card < 2 ^ (evens n p).card := by
  have hpos : ∀ i, 0 < step^[i] n := fun i => iterate_pos hc.1 i
  have hO : 0 < ∏ i ∈ odds n p, step^[i] n := prod_pos fun i _ => hpos i
  have hlt : 3 ^ (odds n p).card * ∏ i ∈ odds n p, step^[i] n
      < 2 ^ (evens n p).card * ∏ i ∈ odds n p, step^[i] n := by
    rw [cycle_identity hc, ← prod_const, ← prod_mul_distrib]
    exact prod_lt_prod_of_nonempty₀ (fun i _ => by have := hpos i; positivity)
      (fun i _ => by omega) (odds_nonempty hc)
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Upper bound.** If every odd element of the cycle is `≥ m`, then `m^b 2^a ≤ (3m+1)^b`. -/
theorem two_pow_le {n p m : ℕ} (hc : IsCycle n p)
    (hm : ∀ i ∈ odds n p, m ≤ step^[i] n) :
    m ^ (odds n p).card * 2 ^ (evens n p).card ≤ (3 * m + 1) ^ (odds n p).card := by
  have hpos : ∀ i, 0 < step^[i] n := fun i => iterate_pos hc.1 i
  have hO : 0 < ∏ i ∈ odds n p, step^[i] n := prod_pos fun i _ => hpos i
  have hle : m ^ (odds n p).card * 2 ^ (evens n p).card * ∏ i ∈ odds n p, step^[i] n
      ≤ (3 * m + 1) ^ (odds n p).card * ∏ i ∈ odds n p, step^[i] n := by
    rw [mul_assoc, cycle_identity hc, ← prod_const, ← prod_const, ← prod_mul_distrib,
      ← prod_mul_distrib]
    refine prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i hi => ?_)
    have := hm i hi
    nlinarith
  exact Nat.le_of_mul_le_mul_right hle hO

/-- If `n` lies on a cycle and does not reach `1`, then no element of its orbit reaches `1`. -/
lemma not_reachesOne_iterate {n : ℕ} (h : ¬ ReachesOne n) (i : ℕ) :
    ¬ ReachesOne (step^[i] n) := fun h' => h (ReachesOne.of_iterate h')

/-- Every `1 ≤ y < 1024` reaches `1` (from the kernel-checked verification). -/
lemma reachesOne_lt_1024 {y : ℕ} (h1 : 1 ≤ y) (h2 : y < 1024) : ReachesOne y :=
  reachesOne_of_descends_below 1023 (fun m hm hm' => descends_small m hm (by omega)) y h1
    (by omega)

/-- Exponent bound: the upper bound forces `a ≤ 2b`. -/
lemma evens_le_two_mul {m a b : ℕ} (hm : 1 ≤ m) (h : m ^ b * 2 ^ a ≤ (3 * m + 1) ^ b) :
    a ≤ 2 * b := by
  have h4 : (3 * m + 1) ^ b ≤ m ^ b * 2 ^ (2 * b) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num; omega) b
  have hmb : 0 < m ^ b := by positivity
  have : 2 ^ a ≤ 2 ^ (2 * b) := Nat.le_of_mul_le_mul_left (h.trans h4) hmb
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

/-- Checker: no `(a, b)` with `1 ≤ b < B`, `a ≤ 2b` satisfies both cycle inequalities. -/
def noCycleExponents (N B : ℕ) : Bool :=
  (List.range B).all fun b => b == 0 || (List.range (2 * b + 1)).all fun a =>
    !(decide (3 ^ b < 2 ^ a) && decide (N ^ b * 2 ^ a ≤ (3 * N + 1) ^ b))

theorem noCycleExponents_1024 : noCycleExponents 1024 41 = true := by decide +kernel

/-- **Main theorem.** A cycle not containing `1` has at least 41 odd steps. -/
theorem odds_card_ge {n p : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n) :
    41 ≤ (odds n p).card := by
  have hm : ∀ i ∈ odds n p, 1024 ≤ step^[i] n := by
    intro i _
    by_contra hlt
    exact not_reachesOne_iterate hnr i (reachesOne_lt_1024 (iterate_pos hc.1 i) (by omega))
  have hup := two_pow_le hc hm
  have hlow := three_pow_lt_two_pow hc
  have ha := evens_le_two_mul (by norm_num) hup
  by_contra hb
  have hchk := noCycleExponents_1024
  simp only [noCycleExponents, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hchk
  rcases hchk _ (by omega : (odds n p).card < 41) with h0 | h
  · exact absurd h0 (Nat.pos_iff_ne_zero.1 (card_pos.2 (odds_nonempty hc)))
  · rcases h (evens n p).card (by omega) with h' | h'
    · exact h' hlow
    · exact h' hup

/-- A cycle not containing `1` has at least 65 even steps. -/
theorem evens_card_ge {n p : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n) :
    65 ≤ (evens n p).card := by
  have h1 : 2 ^ 64 < 3 ^ 41 := by norm_num
  have h2 : 3 ^ 41 ≤ 3 ^ (odds n p).card := Nat.pow_le_pow_right (by norm_num) (odds_card_ge hc hnr)
  have h3 := three_pow_lt_two_pow hc
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (by omega : 2 ^ 64 < 2 ^ (evens n p).card)

/-- **Cycle length bound.** Any cycle not containing `1` has length at least 106. -/
theorem cycle_length_ge {n p : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n) : 106 ≤ p := by
  have := card_evens_add_card_odds n p
  have := odds_card_ge hc hnr
  have := evens_card_ge hc hnr
  omega

end Collatz
