import Collatz.StoppingTime

/-!
# Integers with long finite stopping times (Applegate-Lagarias method)

Backward moves from a node `a` with `3 ∤ a`: the even move `a' = 2a`, and the odd move
`a' = (2a - 1)/3` when `a ≡ 2, 8 (mod 9)`; in both cases `T a' = a` and `3 ∤ a'`. A potential `lh`
on the residues mod `243` (values `0..13`, from `scripts/longstop_cert.py`) satisfies, for every
residue mod `729`, `lh a + 2 ≤ lh a' + 5 [odd move]` for some admissible move (`lcert`, checked by
`decide`). Following such moves backwards from `4` for `L` steps gives `n` with

* `T^(L+2) n = 1` and `T^i n ≠ 1` for `i < L + 2` (total stopping time exactly `L + 2`),
* at least `(2L - 13)/5` odd steps, hence `3^s n ≤ 2^(L+2)`.

So `(5 log 2 - 2 log 3) σ(n) ≥ 5 log n - 17 log 3`: infinitely many `n` reach `1` only after
`σ(n) ≥ γ log n - c` steps with `γ = 1 / (log 2 - (2/5) log 3) ≈ 3.94` (the trivial bound is
`1 / log 2 ≈ 1.44`). Applegate and Lagarias (2003) proved `γ ≥ 6.14316` with a far larger
certificate of the same kind.
-/

namespace Collatz

/-- The potential on residues mod `243`. -/
def LH : List ℕ := [0, 7, 9, 0, 6, 9, 0, 5, 8, 0, 11, 7, 0, 10, 7, 0, 3, 10, 0, 6, 13, 0, 8, 3, 0, 2, 12, 0, 9, 9, 0, 5, 5, 0, 3, 6, 0, 8, 8, 0, 9, 7, 0, 3, 10, 0, 5, 9, 0, 7, 4, 0, 3, 8, 0, 5, 11, 0, 3, 9, 0, 3, 7, 0, 7, 6, 0, 9, 5, 0, 4, 12, 0, 4, 10, 0, 10, 2, 0, 0, 11, 0, 9, 8, 0, 6, 5, 0, 4, 9, 0, 10, 7, 0, 11, 6, 0, 3, 9, 0, 6, 9, 0, 11, 5, 0, 3, 13, 0, 8, 7, 0, 4, 5, 0, 2, 5, 0, 11, 9, 0, 11, 5, 0, 7, 11, 0, 5, 9, 0, 8, 4, 0, 1, 11, 0, 7, 10, 0, 4, 6, 0, 5, 9, 0, 7, 6, 0, 6, 3, 0, 7, 12, 0, 4, 11, 0, 10, 2, 0, 0, 13, 0, 6, 11, 0, 7, 8, 0, 4, 8, 0, 7, 9, 0, 11, 6, 0, 3, 11, 0, 7, 12, 0, 9, 3, 0, 2, 13, 0, 8, 8, 0, 7, 5, 0, 1, 7, 0, 9, 8, 0, 11, 4, 0, 6, 13, 0, 7, 9, 0, 9, 5, 0, 1, 9, 0, 6, 10, 0, 5, 7, 0, 2, 6, 0, 7, 7, 0, 7, 4, 0, 5, 13, 0, 5, 13, 0, 11, 3, 0, 1, 13]

def lh (r : ℕ) : ℕ := LH.getD r 0

theorem lcert : ∀ t < 729, t % 3 ≠ 0 →
    (lh (t % 243) + 2 ≤ lh ((2 * t) % 243) ∨
      ((t % 9 = 2 ∨ t % 9 = 8) ∧ lh (t % 243) + 2 ≤ lh (((2 * t - 1) / 3) % 243) + 5)) := by
  decide +kernel

theorem lh_le : ∀ r < 243, lh r ≤ 13 := by decide +kernel

/-- Backward paths with many odd moves. -/
theorem backward_path : ∀ L a, a % 3 ≠ 0 → ∃ n, n % 3 ≠ 0 ∧ kstepT^[L] n = a ∧
    2 * L + lh (a % 243) ≤ 5 * oddCount L n + lh (n % 243)
  | 0, a, ha => ⟨a, ha, rfl, by simp [oddCount]⟩
  | L + 1, a, ha => by
    have hc := lcert (a % 729) (Nat.mod_lt _ (by norm_num)) (by omega)
    rw [show a % 729 % 243 = a % 243 by omega,
      show 2 * (a % 729) % 243 = 2 * a % 243 by omega] at hc
    rcases hc with h | ⟨h9, h⟩
    · obtain ⟨n, hn3, hnT, hb⟩ := backward_path L (2 * a) (by omega)
      refine ⟨n, hn3, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hnT, kstepT_of_even (by omega)]; omega
      · rw [oddCount_succ, hnT, show 2 * a % 2 = 0 by omega]
        omega
    · have h9' : a % 9 = 2 ∨ a % 9 = 8 := by omega
      have e1 : (2 * (a % 729) - 1) / 3 % 243 = (2 * a - 1) / 3 % 243 := by omega
      rw [e1] at h
      obtain ⟨n, hn3, hnT, hb⟩ := backward_path L ((2 * a - 1) / 3) (by omega)
      have hodd : (2 * a - 1) / 3 % 2 = 1 := by omega
      refine ⟨n, hn3, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hnT, kstepT_of_odd hodd]; omega
      · rw [oddCount_succ, hnT, hodd]
        omega

lemma iterate_one_mem : ∀ m, kstepT^[m] 1 = 1 ∨ kstepT^[m] 1 = 2
  | 0 => Or.inl rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    rcases iterate_one_mem m with h | h <;> rw [h]
    · right; rfl
    · left; rfl

/-- **For every `L` some `n` reaches `1` after exactly `L + 2` steps with many odd steps.** -/
theorem exists_long_stopping (L : ℕ) : ∃ n, kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧ 2 * L ≤ 5 * oddCount L n + 13 ∧
    3 ^ oddCount L n * n ≤ 2 ^ (L + 2) := by
  obtain ⟨n, -, hnT, hb⟩ := backward_path L 4 (by norm_num)
  have h4 : kstepT 4 = 2 := rfl
  have h2 : kstepT 2 = 1 := rfl
  have hlh := lh_le (n % 243) (Nat.mod_lt _ (by norm_num))
  refine ⟨n, ?_, ?_, by omega, ?_⟩
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hnT, h4, h2]
  · intro i hi h1
    rcases Nat.lt_or_ge i (L + 1) with hiL | hiL
    · have : kstepT^[L] n = kstepT^[L - i] 1 := by
        rw [← h1, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      rw [hnT] at this
      rcases iterate_one_mem (L - i) with h | h <;> omega
    · rw [show i = L + 1 by omega, Function.iterate_succ_apply', hnT, h4] at h1
      omega
  · have := iterate_lower n L
    rw [hnT] at this
    calc 3 ^ oddCount L n * n ≤ 2 ^ L * 4 := this
      _ = 2 ^ (L + 2) := by ring

/-- The logarithmic form: `(5 log 2 - 2 log 3) σ ≥ 5 log n - 17 log 3` with `σ = L + 2`. -/
theorem long_stopping_log (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    5 * Real.log n - 17 * Real.log 3 ≤ (5 * Real.log 2 - 2 * Real.log 3) * (L + 2 : ℕ) := by
  obtain ⟨n, h1, hne, hodd, hsize⟩ := exists_long_stopping L
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : kstepT^[L + 2] 0 = 0 := Function.iterate_fixed rfl _
      omega
    · exact h0
  refine ⟨n, hn, h1, hne, ?_⟩
  set s := oddCount L n
  have hsR : ((3 : ℝ) ^ s * n) ≤ 2 ^ (L + 2) := by exact_mod_cast hsize
  have hl := Real.log_le_log (by positivity) hsR
  rw [Real.log_mul (by positivity) (by exact_mod_cast (show n ≠ 0 by omega)), Real.log_pow,
    Real.log_pow] at hl
  have hoddR : (2 * L : ℝ) ≤ 5 * s + 13 := by exact_mod_cast hodd
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  push_cast at hl ⊢
  nlinarith [mul_le_mul_of_nonneg_right hoddR h3.le]

end Collatz
