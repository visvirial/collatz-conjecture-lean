import Collatz.Korec

/-!
# The distribution of stopping times (Terras 1976)

For the accelerated map `T`, `n` has stopping time `≤ k` if `T^j n < n` for some
`1 ≤ j ≤ k`. The residue `r` mod `2^k` has coefficient stopping time `≤ k` if
`3^(s_j r) < 2^j` for some `1 ≤ j ≤ k`; these residues form `goodSet k`.

* `stopsBy_imp`: stopping time `≤ k` implies coefficient stopping time `≤ k` (all `n ≥ 1`);
* `imp_stopsBy`: the converse holds for `n ≥ 3^k`;
* `density_stopsBy`: the set of `n` with stopping time `≤ k` has natural density exactly
  `#(goodSet k) / 2^k`, e.g. `1/2, 3/4, 3/4, 13/16` for `k = 1, 2, 3, 4`.

As `k → ∞` these densities tend to `1` (Terras' theorem, `density_not_descends`).
-/

namespace Collatz

open Finset

/-- Residues mod `2^k` with coefficient stopping time at most `k`. -/
def goodSet (k : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun r => ∃ j ∈ Icc 1 k, 3 ^ oddCount j r < 2 ^ j)

theorem goodSet_card_one : (goodSet 1).card = 1 := by decide
theorem goodSet_card_two : (goodSet 2).card = 3 := by decide
theorem goodSet_card_three : (goodSet 3).card = 6 := by decide
theorem goodSet_card_four : (goodSet 4).card = 13 := by decide

lemma iterate_lower (n : ℕ) : ∀ j, 3 ^ oddCount j n * n ≤ 2 ^ j * kstepT^[j] n
  | 0 => by simp [oddCount]
  | j + 1 => by
    have ih := iterate_lower n j
    rw [Function.iterate_succ_apply', oddCount_succ, pow_succ 2 j]
    generalize kstepT^[j] n = x at ih ⊢
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [h, Nat.add_zero, kstepT_of_even h]
      have : 2 * (x / 2) = x := by omega
      calc 3 ^ oddCount j n * n ≤ 2 ^ j * x := ih
        _ = 2 ^ j * 2 * (x / 2) := by rw [mul_assoc, this]
    · rw [h, kstepT_of_odd h, pow_succ]
      have : 2 * ((3 * x + 1) / 2) = 3 * x + 1 := by omega
      calc 3 ^ oddCount j n * 3 * n = 3 * (3 ^ oddCount j n * n) := by ring
        _ ≤ 3 * (2 ^ j * x) := Nat.mul_le_mul_left _ ih
        _ ≤ 2 ^ j * (3 * x + 1) := by
          rw [show 2 ^ j * (3 * x + 1) = 3 * (2 ^ j * x) + 2 ^ j by ring]; exact Nat.le_add_right _ _
        _ = 2 ^ j * 2 * ((3 * x + 1) / 2) := by rw [mul_assoc, this]

lemma oddCount_mod {k j : ℕ} (hj : j ≤ k) (n : ℕ) : oddCount j n = oddCount j (n % 2 ^ k) := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ k)]
  exact oddCount_affine j hj

/-- A stopping time `≤ k` forces a coefficient stopping time `≤ k`. -/
theorem stopsBy_imp {k n j : ℕ} (hj : j ≤ k) (h : kstepT^[j] n < n) :
    3 ^ oddCount j (n % 2 ^ k) < 2 ^ j := by
  rw [← oddCount_mod hj]
  have h1 := iterate_lower n j
  have hn : 0 < n := by omega
  have : 3 ^ oddCount j n * n < 2 ^ j * n :=
    lt_of_le_of_lt h1 (Nat.mul_lt_mul_of_pos_left h (by positivity))
  exact Nat.lt_of_mul_lt_mul_right this

/-- Conversely, for `n ≥ 3^k` a coefficient stopping time `≤ k` is a stopping time. -/
theorem imp_stopsBy {k n j : ℕ} (hj : j ≤ k) (hn : 3 ^ k ≤ n)
    (hg : 3 ^ oddCount j (n % 2 ^ k) < 2 ^ j) : kstepT^[j] n < n := by
  rw [← oddCount_mod hj] at hg
  have hb := iterate_bound n j
  have h3 : 3 ^ j ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hj
  have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  by_contra hc
  push Not at hc
  have e1 : (3 ^ oddCount j n + 1) * n ≤ 2 ^ j * n := Nat.mul_le_mul_right n hg
  have e2 : 2 ^ j * n ≤ 2 ^ j * kstepT^[j] n := Nat.mul_le_mul_left _ hc
  rw [add_mul, one_mul] at e1
  omega

/-! ## Counting residues -/

lemma card_filter_mod_ge (q N : ℕ) (hq : 0 < q) (S : Finset ℕ) (hS : S ⊆ range q) :
    S.card * (N / q) ≤ ((range N).filter (fun n => n % q ∈ S)).card := by
  rw [← card_range (N / q), ← card_product]
  apply card_le_card_of_injOn (fun p => q * p.2 + p.1)
  · intro p hp
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe] at hp
    have hr : p.1 < q := mem_range.1 (hS hp.1)
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · calc q * p.2 + p.1 < q * p.2 + q := by omega
        _ = q * (p.2 + 1) := by ring
        _ ≤ q * (N / q) := Nat.mul_le_mul_left _ hp.2
        _ ≤ N := Nat.mul_div_le N q
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]; exact hp.1
  · intro a ha b hb h
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe] at ha hb
    have ha1 := mem_range.1 (hS ha.1)
    have hb1 := mem_range.1 (hS hb.1)
    simp only at h
    have h1 : a.1 = b.1 := by
      have := congrArg (· % q) h
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at this
      exact this
    have h2 : a.2 = b.2 := by
      rw [h1] at h
      exact Nat.eq_of_mul_eq_mul_left hq (by omega)
    exact Prod.ext h1 h2

/-! ## The density -/

open Classical in
/-- **Terras**: the integers with stopping time `≤ k` have density `#(goodSet k) / 2^k`. -/
theorem density_stopsBy (k : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ((((range N).filter (fun n => ∃ j ∈ Icc 1 k, kstepT^[j] n < n)).card : ℕ)
        : ℝ) / N)
      Filter.atTop (nhds (((goodSet k).card : ℝ) / 2 ^ k)) := by
  set q := 2 ^ k
  have hq : 0 < q := by positivity
  set G := goodSet k
  set A : ℕ → Finset ℕ := fun N => (range N).filter (fun n => ∃ j ∈ Icc 1 k, kstepT^[j] n < n)
  set B : ℕ → Finset ℕ := fun N => (range N).filter (fun n => n % q ∈ G)
  have hAB : ∀ N, (A N).card ≤ (B N).card := fun N => card_le_card (by
    intro n hn
    simp only [A, B, G, goodSet, mem_filter, mem_range, mem_Icc] at hn ⊢
    obtain ⟨hN, j, ⟨hj1, hjk⟩, hj⟩ := hn
    exact ⟨hN, Nat.mod_lt _ hq, j, ⟨hj1, hjk⟩, stopsBy_imp hjk hj⟩)
  have hBA : ∀ N, (B N).card ≤ (A N).card + 3 ^ k := fun N => by
    have : B N ⊆ A N ∪ range (3 ^ k) := by
      intro n hn
      simp only [A, B, G, goodSet, mem_filter, mem_range, mem_Icc, mem_union] at hn ⊢
      obtain ⟨hN, -, j, ⟨hj1, hjk⟩, hj⟩ := hn
      by_cases h3 : 3 ^ k ≤ n
      · exact Or.inl ⟨hN, j, ⟨hj1, hjk⟩, imp_stopsBy hjk h3 hj⟩
      · exact Or.inr (by omega)
    have := (card_le_card this).trans (card_union_le _ _)
    rwa [card_range] at this
  have hGq : G ⊆ range q := filter_subset _ _
  have hlo : ∀ N, G.card * (N / q) ≤ (B N).card := fun N => card_filter_mod_ge q N hq G hGq
  have hhi : ∀ N, (B N).card ≤ G.card * (N / q + 1) := fun N => card_filter_mod_le q N hq G
  -- real bounds
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have key : ∀ N : ℕ, 1 ≤ N →
      (G.card : ℝ) / q - (G.card + 3 ^ k) / N ≤ ((A N).card : ℝ) / N ∧
      ((A N).card : ℝ) / N ≤ (G.card : ℝ) / q + G.card / N := by
    intro N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hdiv : ((N : ℝ) / q) - 1 ≤ ((N / q : ℕ) : ℝ) := by
      have h1 : ((N / q : ℕ) : ℝ) * q + (N % q : ℕ) = N := by exact_mod_cast Nat.div_add_mod' N q
      have h2 : ((N % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt N hq
      rw [div_sub_one hqR.ne', div_le_iff₀ hqR]; linarith
    have hdiv' : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
      rw [le_div_iff₀ hqR]; exact_mod_cast Nat.div_mul_le_self N q
    have l1 : (G.card : ℝ) * ((N / q : ℕ) : ℝ) ≤ (B N).card := by exact_mod_cast hlo N
    have l2 : ((B N).card : ℝ) ≤ (A N).card + 3 ^ k := by exact_mod_cast hBA N
    have u1 : ((A N).card : ℝ) ≤ (B N).card := by exact_mod_cast hAB N
    have u2 : ((B N).card : ℝ) ≤ G.card * (((N / q : ℕ) : ℝ) + 1) := by exact_mod_cast hhi N
    have hG0 : (0 : ℝ) ≤ G.card := by positivity
    have m1 := mul_le_mul_of_nonneg_left hdiv hG0
    have m2 := mul_le_mul_of_nonneg_left hdiv' hG0
    constructor
    · have hL : (G.card : ℝ) * (N / q) - (G.card + 3 ^ k) ≤ (A N).card := by nlinarith
      calc (G.card : ℝ) / q - (G.card + 3 ^ k) / N
          = ((G.card : ℝ) * (N / q) - (G.card + 3 ^ k)) / N := by field_simp
        _ ≤ ((A N).card : ℝ) / N := div_le_div_of_nonneg_right hL hNR.le
    · have hU : ((A N).card : ℝ) ≤ G.card * (N / q) + G.card := by nlinarith
      calc ((A N).card : ℝ) / N ≤ ((G.card : ℝ) * (N / q) + G.card) / N :=
            div_le_div_of_nonneg_right hU hNR.le
        _ = (G.card : ℝ) / q + G.card / N := by field_simp
  have hlim1 : Filter.Tendsto (fun N : ℕ => (G.card : ℝ) / q - (G.card + 3 ^ k) / N)
      Filter.atTop (nhds ((G.card : ℝ) / q)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat ((G.card : ℝ) + 3 ^ k))
  have hlim2 : Filter.Tendsto (fun N : ℕ => (G.card : ℝ) / q + G.card / N)
      Filter.atTop (nhds ((G.card : ℝ) / q)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (G.card : ℝ))
  have hfin := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim1 hlim2
    (Filter.eventually_atTop.2 ⟨1, fun N hN => (key N hN).1⟩)
    (Filter.eventually_atTop.2 ⟨1, fun N hN => (key N hN).2⟩)
  convert hfin using 3
  simp [q]

end Collatz
