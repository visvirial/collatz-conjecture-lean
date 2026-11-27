import Collatz.Basic

/-!
# Reduction to descent

The Collatz conjecture is equivalent to: every `n > 1` eventually drops strictly below `n`.
This is the standard reduction behind "stopping time" arguments (Terras, Everett).
-/

namespace Collatz

/-- If every `n` with `2 ≤ n ≤ N` descends, then every `n` with `1 ≤ n ≤ N` reaches `1`
(strong induction). -/
theorem reachesOne_of_descends_below (N : ℕ)
    (h : ∀ n, 2 ≤ n → n ≤ N → Descends n) : ∀ n, 1 ≤ n → n ≤ N → ReachesOne n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnN
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact reachesOne_one
    · obtain ⟨k, -, hk⟩ := h n h2 hnN
      exact ReachesOne.of_iterate
        (ih _ hk (iterate_pos (by omega) k) (by omega))

/-- **Reduction.** The Collatz conjecture holds iff every `n ≥ 2` descends. -/
theorem conjecture_iff_descends : Conjecture ↔ ∀ n, 2 ≤ n → Descends n := by
  constructor
  · intro hC n hn
    obtain ⟨k, hk⟩ := hC n (by omega)
    refine ⟨k, ?_, by omega⟩
    rcases k with _ | k
    · simp at hk; omega
    · omega
  · intro hD n hn
    exact reachesOne_of_descends_below n (fun m hm _ => hD m hm) n hn le_rfl

/-- Even numbers `≥ 2` descend in one step. -/
lemma descends_of_even {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) : Descends n :=
  ⟨1, le_rfl, by simp [step_even he]; omega⟩

/-- Numbers `n ≡ 1 (mod 4)`, `n ≥ 5`, descend in three steps: `n ↦ (3n+1)/4`. -/
lemma descends_of_mod_four_eq_one {n : ℕ} (hn : 5 ≤ n) (h : n % 4 = 1) : Descends n := by
  refine ⟨3, by norm_num, ?_⟩
  have h1 : n % 2 = 1 := by omega
  have h2 : (3 * n + 1) % 2 = 0 := by omega
  have h3 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    step_odd h1, step_even h2, step_even h3]
  omega

end Collatz
