import Collatz.Periodic

/-!
# Natural numbers among the 2-adic periodic points

A periodic point of `T` in `ℤ₂` that is a positive integer `n` gives a Collatz cycle: since an
odd `T`-step is two `step`s, `kstepT^[p] n = step^[p + s] n` with `s` odd steps
(`kstepT_iterate_eq_step`), and that `step`-cycle has exactly `p` even and `s` odd steps
(`card_evens_kstepT`, `card_odds_kstepT`). So the `T`-period is the number of even steps of the
cycle, and any lower bound on even steps bounds `p`: `p ≥ 65` from `Collatz.Cycle`
(`natCast_periodic_ge`), and `p ≥ 125743` from the 2^32 verification (`CollatzBig.Bridge`).
(The literature, e.g. Eliahou 1993, counts cycle lengths in this accelerated convention.)
-/

namespace Collatz

lemma kstepT_iterate_eq_step (n : ℕ) : ∀ j, kstepT^[j] n = step^[j + oddCount j n] n
  | 0 => by simp [oddCount]
  | j + 1 => by
    rw [Function.iterate_succ_apply', oddCount_succ, kstepT_iterate_eq_step n j]
    generalize hy : step^[j + oddCount j n] n = y
    have e : j + 1 + (oddCount j n + y % 2) = (1 + y % 2) + (j + oddCount j n) := by ring
    rw [e, Function.iterate_add_apply, hy]
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · rw [h, kstepT_of_even h]
      simp [step_even h]
    · rw [h, kstepT_of_odd h]
      simp only [Nat.reduceAdd, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
        id_eq]
      rw [step_odd h, step_even (by omega)]

lemma card_odds_eq_sum (n L : ℕ) : (odds n L).card = ∑ i ∈ Finset.range L, step^[i] n % 2 := by
  rw [odds, Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (step^[i] n) with h | h <;> simp [h]

/-- The first `j + s_j` `step`s contain exactly `s_j` odd values. -/
theorem card_odds_kstepT (n : ℕ) : ∀ j, (odds n (j + oddCount j n)).card = oddCount j n
  | 0 => by simp [oddCount, odds]
  | j + 1 => by
    rw [card_odds_eq_sum]
    have ih := card_odds_kstepT n j
    rw [card_odds_eq_sum] at ih
    rw [oddCount_succ, kstepT_iterate_eq_step n j]
    generalize hy : step^[j + oddCount j n] n = y
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · rw [h, show j + 1 + (oddCount j n + 0) = (j + oddCount j n) + 1 by ring,
        Finset.sum_range_succ, ih, hy, h]
    · rw [h, show j + 1 + (oddCount j n + 1) = (j + oddCount j n) + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, hy, h, Function.iterate_succ_apply',
        hy, step_odd h]
      have : (3 * y + 1) % 2 = 0 := by omega
      rw [this]

/-- ... and exactly `j` even values. -/
theorem card_evens_kstepT (n j : ℕ) : (evens n (j + oddCount j n)).card = j := by
  have h1 := card_evens_add_card_odds n (j + oddCount j n)
  rw [card_odds_kstepT] at h1
  omega

theorem isCycle_of_kstepT_periodic {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : kstepT^[p] n = n) : IsCycle n (p + oddCount p n) :=
  ⟨hn, by omega, by rw [← kstepT_iterate_eq_step, h]⟩

/-- A lower bound `E` on the even steps of nontrivial cycles bounds `T`-periods: `E ≤ p`. -/
theorem kstepT_period_ge {E : ℕ}
    (hE : ∀ n p, IsCycle n p → ¬ ReachesOne n → E ≤ (evens n p).card)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : kstepT^[p] n = n) (hnr : ¬ ReachesOne n) :
    E ≤ p := by
  have := hE _ _ (isCycle_of_kstepT_periodic hn hp h) hnr
  rwa [card_evens_kstepT] at this

/-- The same in `ℤ₂`: a positive integer that is a periodic point of `T` of period `p` and does
not reach `1` has `E ≤ p`. -/
theorem natCast_periodic_ge_of {E : ℕ}
    (hE : ∀ n p, IsCycle n p → ¬ ReachesOne n → E ≤ (evens n p).card)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : TwoAdic.T^[p] (n : ℤ_[2]) = n)
    (hnr : ¬ ReachesOne n) : E ≤ p := by
  rw [TwoAdic.T_iterate_natCast] at h
  exact kstepT_period_ge hE hn hp (Nat.cast_injective h) hnr

theorem natCast_periodic_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : TwoAdic.T^[p] (n : ℤ_[2]) = n) (hnr : ¬ ReachesOne n) : 65 ≤ p :=
  natCast_periodic_ge_of (fun _ _ hc hr => evens_card_ge hc hr) hn hp h hnr

end Collatz
