import Mathlib
import Collatz.Defs

/-!
# The Collatz map: basic definitions

We define the Collatz map `step`, the predicate `ReachesOne`, and the statement of the
Collatz conjecture as a `Prop`. The conjecture itself is *not* proved anywhere in this
library; we only prove reductions and partial results about it.
-/

namespace Collatz

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3n + 1` if `n` is odd. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` eventually reaches `1` under iteration of `step`. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, step^[k] n = 1

/-- The Collatz conjecture. -/
def Conjecture : Prop := ∀ n, 1 ≤ n → ReachesOne n

/-- `n` eventually drops strictly below itself (after at least one step). -/
def Descends (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ step^[k] n < n

lemma step_even {n : ℕ} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

lemma step_odd {n : ℕ} (h : n % 2 = 1) : step n = 3 * n + 1 := by
  simp [step, h]

lemma step_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ step n := by
  unfold step
  split_ifs with h <;> omega

lemma iterate_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ step^[k] n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (step_pos hn)

lemma step_one : step 1 = 4 := rfl

/-- Once at `1`, the orbit cycles `1 → 4 → 2 → 1`. -/
lemma reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩

lemma ReachesOne.of_iterate {n k : ℕ} (h : ReachesOne (step^[k] n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [Function.iterate_add_apply, hj]⟩

lemma ReachesOne.of_step {n : ℕ} (h : ReachesOne (step n)) : ReachesOne n :=
  ReachesOne.of_iterate (k := 1) h

lemma reachesOne_pow_two (e : ℕ) : ReachesOne (2 ^ e) := by
  induction e with
  | zero => exact reachesOne_one
  | succ e ih =>
    apply ReachesOne.of_step
    rw [step_even (by simp [pow_succ])]
    simpa [pow_succ] using ih

end Collatz
