import Collatz.Residue

/-!
# Finite verification

A boolean checker for descent of a single number, proved sound, and a kernel-checked
verification of descent for all `2 ≤ n < 2^10`. We use `decide +kernel` (no `native_decide`),
so no extra axioms beyond the standard ones are introduced.
-/

namespace Collatz

/-- Iterate from `x` for at most `fuel` steps, checking whether we drop below `n0`. -/
def descAux (n0 : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, x => decide (step x < n0) || descAux n0 fuel (step x)

lemma descAux_spec {n0 : ℕ} :
    ∀ {fuel x : ℕ}, descAux n0 fuel x = true → ∃ j, 1 ≤ j ∧ step^[j] x < n0
  | 0, _, h => by simp [descAux] at h
  | fuel + 1, x, h => by
    simp only [descAux, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨1, le_rfl, by simpa using h⟩
    · obtain ⟨j, hj, he⟩ := descAux_spec h
      exact ⟨j + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

/-- Check that every `n` with `2 ≤ n < N` descends within `fuel` steps. -/
def checkRange (N fuel : ℕ) : Bool :=
  (List.range N).all (fun n => decide (n < 2) || descAux n fuel n)

theorem descends_of_checkRange {N fuel : ℕ} (h : checkRange N fuel = true) :
    ∀ n, 2 ≤ n → n < N → Descends n := by
  intro n h2 hN
  simp only [checkRange, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h n hN with h' | h'
  · omega
  · exact descAux_spec h'

theorem checkRange_1024 : checkRange (2 ^ 10) 200 = true := by decide +kernel

theorem descends_small : ∀ n, 2 ≤ n → n < 2 ^ 10 → Descends n :=
  descends_of_checkRange checkRange_1024

end Collatz
