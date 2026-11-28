import Collatz

/-!
# Headline statements

The main theorems of the README, restated as `example`s so that the README cannot drift from
the Lean statements. Each `example` is closed by the named theorem.
-/

open Collatz Finset
open scoped Collatz.TwoAdic

example : Conjecture ↔ ∀ n, 2 ^ 10 ≤ n → n % 2 ^ 10 ∈ survivors 10 → Descends n :=
  conjecture_iff_survivors_descend
example : (survivors 10).length = 64 := survivors_ten_length

example {n p : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n) : 106 ≤ p := cycle_length_ge hc hnr

open Classical in
example (q : ℕ) : ∃ N0, ∀ N ≥ N0, q * ((range N).filter (fun n => ¬ Descends n)).card ≤ N :=
  almost_all_descend q

open Classical in
example {c : ℝ} (hc : Real.log 3 / Real.log 4 < c) (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * ((range N).filter (fun n : ℕ => ∀ j, (n : ℝ) ^ c ≤ ((step^[j] n : ℕ) : ℝ))).card ≤ N :=
  korec hc q

open Classical in
example : ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
    κ * (N : ℝ) ^ ((3 : ℝ) / 7) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) :=
  card_reachesOne_ge_three_sevenths

open Classical in
example : ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
    κ * (N : ℝ) ^ ((303 : ℝ) / 625) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) :=
  card_reachesOne_ge_rpow_krasikov

example (x : ℤ_[2]) : TwoAdic.Qequiv (TwoAdic.T x) = TwoAdic.shift (TwoAdic.Qequiv x) :=
  TwoAdic.Qequiv_conj x
example {p : ℕ} (hp : 1 ≤ p) : Nat.card {x : ℤ_[2] // TwoAdic.T^[p] x = x} = 2 ^ p :=
  TwoAdic.card_periodic hp
example : Ergodic TwoAdic.T TwoAdic.μ := TwoAdic.T_ergodic

example {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : TwoAdic.T^[p] (n : ℤ_[2]) = n)
    (hnr : ¬ ReachesOne n) : 65 ≤ p := natCast_periodic_ge hn hp h hnr

example : (goodSet 100).card = 2 ^ 100 - 302560669500543257546172187 := goodSet_card_hundred

example (k : ℕ) : 1 - ((goodSet k).card : ℝ) / 2 ^ k ≤
    Real.exp (-((Real.log 2 - Real.binEntropy theta) * k)) := density_tail_le k

example (L : ℕ) : ∃ n, kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    2 * L ≤ 5 * oddCount L n + 13 ∧ 3 ^ oddCount L n * n ≤ 2 ^ (L + 2) := exists_long_stopping L

example (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    20 * Real.log n - 107 * Real.log 3 ≤ (20 * Real.log 2 - 9 * Real.log 3) * (L + 2 : ℕ) :=
  long_stopping_log_ten L

example (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    13 * Real.log n - 85 * Real.log 3 ≤ (13 * Real.log 2 - 6 * Real.log 3) * (L + 2 : ℕ) :=
  long_stopping_log_twelve L

example (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    19 * Real.log n - 145 * Real.log 3 ≤ (19 * Real.log 2 - 9 * Real.log 3) * (L + 2 : ℕ) :=
  long_stopping_log_fifteen L

example : Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, (3 : ℤ_[2]) * TwoAdic.Q (n : ℤ_[2]) = z :=
  TwoAdic.conjecture_iff_three_mul_Q
example {A B : Set ℤ_[2]} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto (fun n => TwoAdic.μ (A ∩ TwoAdic.T^[n] ⁻¹' B)) Filter.atTop
      (nhds (TwoAdic.μ A * TwoAdic.μ B)) := TwoAdic.T_mixing hA hB

example {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 1636) : n = 1 ∧ k = 1 ∧ l = 1 :=
  no_circuit_lt_1636 hc hk

/-! More headline statements. -/

example {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 3)
    (hk : oddCount K n < 306) : ReachesOne n := reachesOne_of_mcycle_three hn hK hper hm hk

example (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => fun i : Fin k => decide (kstepT^[i] r % 2 = 1)) :=
  parity_bijective k

open Classical in
example : Filter.Tendsto (fun N : ℕ => ((((range N).filter (fun n => ¬ Descends n)).card : ℕ) : ℝ) / N)
    Filter.atTop (nhds 0) := density_not_descends

open Classical in
example (k : ℕ) : Filter.Tendsto
    (fun N : ℕ => ((((range N).filter (fun n => ∃ j ∈ Icc 1 k, kstepT^[j] n < n)).card : ℕ) : ℝ) / N)
    Filter.atTop (nhds (((goodSet k).card : ℝ) / 2 ^ k)) := density_stopsBy k

example (k n n' : ℕ) : parityVec k n = parityVec k n' ↔ n % 2 ^ k = n' % 2 ^ k :=
  parityVec_eq_iff k n n'

example (n j : ℕ) : (evens n (j + oddCount j n)).card = j := card_evens_kstepT n j

open Classical in
example (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) ^ (Real.log 2 / Real.log 86) ≤
    2 * (((range (N + 1)).filter ReachesOne).card : ℝ) := card_reachesOne_ge_rpow N hN

namespace Collatz.TwoAdic

open MeasureTheory ProbabilityTheory Filter Topology

example {p : ℕ} (hp : 1 ≤ p) {x : ℤ_[2]} (hx : T^[p] x = x) :
    ∃ a b : ℤ, Odd b ∧ (b : ℤ_[2]) * x = a := periodic_rational hp hx
example : MeasurePreserving T μ μ := T_measurePreserving
example : MeasurePreserving paritySeq μ bernoulli := paritySeq_measurePreserving
example : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (oddCount2 n x : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  odd_fraction_ae
example {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (1 / 4)) P') :
    TendstoInDistribution (fun (n : ℕ) (x : ℤ_[2]) => ((oddCount2 n x : ℝ) - n / 2) / √n)
      atTop Z (fun _ => μ) P' := oddCount2_clt hZ
example : ∀ᵐ x ∂μ, ∀ k d : ℕ, d < 2 ^ k →
    Tendsto (fun n : ℕ => ((((range n).filter (fun i => (T^[i] x).appr k = d)).card : ℕ) : ℝ) / n)
      atTop (𝓝 ((2 : ℝ) ^ k)⁻¹) := orbit_equidistributed_mod
example {S : Set ℤ_[2]} (hS : ∀ n, ∃ E, MeasurableSet E ∧ S = T^[n] ⁻¹' E) : μ S = 0 ∨ μ S = 1 :=
  T_exact hS
example {n : ℕ} (hn : 1 ≤ n) : ReachesOne n ↔ ∃ z : ℤ, (3 : ℤ_[2]) * Q (n : ℤ_[2]) = z :=
  reachesOne_iff_three_mul_Q hn

end Collatz.TwoAdic

-- K. M. Monks 2006: the conjecture on one arithmetic progression suffices
example (a d : ℕ) (hd : 1 ≤ d) :
    Conjecture ↔ ∀ n, 1 ≤ a + d * n → ReachesOne (a + d * n) :=
  MonksAP.conjecture_iff_arith_prog a d hd

open Collatz

/-! Sanity checks on the definitions. -/

example : ReachesOne 27 := ⟨111, by decide +kernel⟩
example : ¬ Descends 1 := by
  rintro ⟨k, -, hk⟩
  have := iterate_pos (le_refl 1) k
  omega
example : IsCycle 1 3 := ⟨le_refl 1, by norm_num, rfl⟩
