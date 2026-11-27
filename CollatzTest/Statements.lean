import Collatz

/-!
# Headline statements

The main theorems of the README, restated as `example`s so that the README cannot drift from
the Lean statements. Each `example` is closed by the named theorem.
-/

open Collatz Finset

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

/-! Sanity checks on the definitions. -/

example : ReachesOne 27 := ⟨111, by decide +kernel⟩
example : ¬ Descends 1 := by
  rintro ⟨k, -, hk⟩
  have := iterate_pos (le_refl 1) k
  omega
example : IsCycle 1 3 := ⟨le_refl 1, by norm_num, rfl⟩
