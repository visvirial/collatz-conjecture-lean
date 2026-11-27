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

example : Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, (3 : ℤ_[2]) * TwoAdic.Q (n : ℤ_[2]) = z :=
  TwoAdic.conjecture_iff_three_mul_Q
example {A B : Set ℤ_[2]} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto (fun n => TwoAdic.μ (A ∩ TwoAdic.T^[n] ⁻¹' B)) Filter.atTop
      (nhds (TwoAdic.μ A * TwoAdic.μ B)) := TwoAdic.T_mixing hA hB

example {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 1636) : n = 1 ∧ k = 1 ∧ l = 1 :=
  no_circuit_lt_1636 hc hk

/-! Sanity checks on the definitions. -/

example : ReachesOne 27 := ⟨111, by decide +kernel⟩
example : ¬ Descends 1 := by
  rintro ⟨k, -, hk⟩
  have := iterate_pos (le_refl 1) k
  omega
example : IsCycle 1 3 := ⟨le_refl 1, by norm_num, rfl⟩
