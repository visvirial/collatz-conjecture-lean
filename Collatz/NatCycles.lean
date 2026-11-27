import Collatz.Periodic

/-!
# Natural numbers among the 2-adic periodic points

A periodic point of `T` in `ℤ₂` that is a positive integer `n` gives a Collatz cycle: since an
odd `T`-step is two `step`s, `kstepT^[p] n = step^[p + s] n` with `s ≤ p` odd steps
(`kstepT_iterate_eq_step`). So any lower bound `L` on the length of nontrivial Collatz cycles
gives `L ≤ 2p` for the `T`-period `p`. With the bound `106` proved in `Collatz.Cycle` this gives
`p ≥ 53` (`natCast_periodic_ge`); `CollatzBig.Bridge` gives `p ≥ 102539` from the 2^32 bound.
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

theorem isCycle_of_kstepT_periodic {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : kstepT^[p] n = n) : IsCycle n (p + oddCount p n) :=
  ⟨hn, by omega, by rw [← kstepT_iterate_eq_step, h]⟩

/-- A lower bound `L` on nontrivial cycle lengths bounds `T`-periods by `L ≤ 2p`. -/
theorem kstepT_period_ge {L : ℕ} (hL : ∀ n p, IsCycle n p → ¬ ReachesOne n → L ≤ p)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : kstepT^[p] n = n) (hnr : ¬ ReachesOne n) :
    L ≤ 2 * p := by
  have := hL _ _ (isCycle_of_kstepT_periodic hn hp h) hnr
  have := oddCount_le p n
  omega

/-- The same in `ℤ₂`: a positive integer that is a periodic point of `T` of period `p` and does
not reach `1` has `L ≤ 2p`. -/
theorem natCast_periodic_ge_of {L : ℕ} (hL : ∀ n p, IsCycle n p → ¬ ReachesOne n → L ≤ p)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : TwoAdic.T^[p] (n : ℤ_[2]) = n)
    (hnr : ¬ ReachesOne n) : L ≤ 2 * p := by
  rw [TwoAdic.T_iterate_natCast] at h
  exact kstepT_period_ge hL hn hp (Nat.cast_injective h) hnr

theorem natCast_periodic_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : TwoAdic.T^[p] (n : ℤ_[2]) = n) (hnr : ¬ ReachesOne n) : 53 ≤ p := by
  have := natCast_periodic_ge_of (L := 106) (fun _ _ hc hr => cycle_length_ge hc hr) hn hp h hnr
  omega

end Collatz
