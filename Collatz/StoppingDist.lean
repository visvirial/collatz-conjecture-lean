import Collatz.StoppingTime

/-!
# The exact distribution of coefficient stopping times

A residue `r` mod `2^k` is *alive* at level `k` if `2^j ≤ 3^(s_j r)` for all `1 ≤ j ≤ k`, i.e. it
is not in `goodSet k`. Let `aliveCount k s` count the alive residues with `s_k r = s`. Pairing
`r` with `2^k + r` (same first `k` parities, opposite parity at step `k`) gives

  `aliveCount (k+1) s = [2^(k+1) ≤ 3^s] (aliveCount k s + aliveCount k (s-1))`,

which `aliveRow` computes in the kernel. Hence `#goodSet k = 2^k - ∑_s aliveRow k s` for every `k`,
and the density of integers with stopping time `≤ k` (`density_stopsBy`) is known exactly, e.g.
for `k = 100` it is `1 - 302560669500543257546172187 / 2^100 ≈ 1 - 2.39 · 10^-4`.
-/

namespace Collatz

open Finset

/-- Not yet stopped (in the coefficient sense) at level `k`. -/
def aliveB (k r : ℕ) : Prop := ∀ j ∈ Icc 1 k, 2 ^ j ≤ 3 ^ oddCount j r

instance (k r : ℕ) : Decidable (aliveB k r) := by unfold aliveB; infer_instance

lemma aliveB_succ (k r : ℕ) :
    aliveB (k + 1) r ↔ aliveB k r ∧ 2 ^ (k + 1) ≤ 3 ^ oddCount (k + 1) r := by
  unfold aliveB
  constructor
  · intro h
    exact ⟨fun j hj => h j (by simp at hj ⊢; omega), h (k + 1) (by simp)⟩
  · rintro ⟨h, hk⟩ j hj
    simp only [mem_Icc] at hj
    rcases Nat.lt_or_ge j (k + 1) with h' | h'
    · exact h j (by simp; omega)
    · rw [show j = k + 1 by omega]; exact hk

lemma aliveB_shift (k r : ℕ) : aliveB k (2 ^ k + r) ↔ aliveB k r := by
  unfold aliveB
  have e : ∀ j ∈ Icc 1 k, oddCount j (2 ^ k + r) = oddCount j r := by
    intro j hj
    rw [show 2 ^ k + r = 2 ^ k * 1 + r by ring]
    exact oddCount_affine j (by simp at hj; omega)
  exact ⟨fun h j hj => (e j hj) ▸ h j hj, fun h j hj => (e j hj).symm ▸ h j hj⟩

lemma not_mem_goodSet {k r : ℕ} (hr : r < 2 ^ k) : r ∉ goodSet k ↔ aliveB k r := by
  simp only [goodSet, mem_filter, mem_range, hr, true_and, not_exists, not_and, not_lt, aliveB]

/-- Generalised pairing: a weight that only depends on `r` mod `2^k`. -/
lemma sum_pair_gen {M : Type*} [AddCommMonoid M] (k : ℕ) (F : ℕ → ℕ → M)
    (hF : ∀ r t, F (2 ^ k + r) t = F r t) :
    ∑ r ∈ range (2 ^ (k + 1)), F r (oddCount (k + 1) r) =
      ∑ r ∈ range (2 ^ k), (F r (oddCount k r) + F r (oddCount k r + 1)) := by
  rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl (fun r _ => ?_)
  rw [hF, oddCount_succ, oddCount_succ, iterate_pow_add,
    show 2 ^ k + r = 2 ^ k * 1 + r by ring, oddCount_affine k le_rfl]
  have h3 := three_pow_mod_two (oddCount k r)
  rcases Nat.mod_two_eq_zero_or_one (kstepT^[k] r) with h | h
  · have hx : (3 ^ oddCount k r + kstepT^[k] r) % 2 = 1 := by omega
    rw [h, hx, Nat.add_zero]
  · have hx : (3 ^ oddCount k r + kstepT^[k] r) % 2 = 0 := by omega
    rw [h, hx, add_comm]; rfl

/-- Alive residues mod `2^k` with `s` odd steps among the first `k`. -/
def aliveCount (k s : ℕ) : ℕ :=
  ((range (2 ^ k)).filter (fun r => aliveB k r ∧ oddCount k r = s)).card

lemma aliveCount_eq_sum (k s : ℕ) :
    aliveCount k s = ∑ r ∈ range (2 ^ k), if aliveB k r ∧ oddCount k r = s then 1 else 0 := by
  rw [aliveCount, card_filter]

theorem aliveCount_succ (k s : ℕ) :
    aliveCount (k + 1) s = if 2 ^ (k + 1) ≤ 3 ^ s then
      aliveCount k s + (if s = 0 then 0 else aliveCount k (s - 1)) else 0 := by
  classical
  rw [aliveCount_eq_sum]
  have e1 : ∀ r, (if aliveB (k + 1) r ∧ oddCount (k + 1) r = s then 1 else 0) =
      (fun r t => if aliveB k r ∧ 2 ^ (k + 1) ≤ 3 ^ t ∧ t = s then (1 : ℕ) else 0) r
        (oddCount (k + 1) r) := by
    intro r
    simp only [aliveB_succ]
    congr 1
    apply propext
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [sum_congr rfl (fun r _ => e1 r), sum_pair_gen k
    (fun r t => if aliveB k r ∧ 2 ^ (k + 1) ≤ 3 ^ t ∧ t = s then (1 : ℕ) else 0)
    (fun r t => by simp only [aliveB_shift])]
  simp only [sum_add_distrib]
  by_cases hc : 2 ^ (k + 1) ≤ 3 ^ s
  · rw [ite_eq_left hc, aliveCount_eq_sum]
    congr 1
    · refine sum_congr rfl (fun r _ => ?_)
      by_cases h : aliveB k r ∧ oddCount k r = s
      · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2 ▸ hc, h.2⟩]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, h'.2.2⟩)]
    · split_ifs with hs
      · refine sum_eq_zero (fun r _ => ?_)
        rw [ite_eq_right (fun h' => by omega)]
      · rw [aliveCount_eq_sum]
        refine sum_congr rfl (fun r _ => ?_)
        by_cases h : aliveB k r ∧ oddCount k r = s - 1
        · rw [ite_eq_left h, ite_eq_left ⟨h.1, by rw [show oddCount k r + 1 = s by omega]; exact hc,
            by omega⟩]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, by omega⟩)]
  · rw [ite_eq_right hc]
    have z : ∀ t, ¬ (2 ^ (k + 1) ≤ 3 ^ t ∧ t = s) := fun t h => hc (h.2 ▸ h.1)
    rw [sum_eq_zero (fun r _ => ite_eq_right (fun h => z _ ⟨h.2.1, h.2.2⟩)),
      sum_eq_zero (fun r _ => ite_eq_right (fun h => z _ ⟨h.2.1, h.2.2⟩))]
    rfl

/-- The table `s ↦ aliveCount k s`, computed by the recursion (kernel friendly). -/
def aliveRow (k : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [1]
    (fun k row => (List.range (k + 2)).map (fun s =>
      if 2 ^ (k + 1) ≤ 3 ^ s then row.getD s 0 + (if s = 0 then 0 else row.getD (s - 1) 0)
      else 0)) k

lemma aliveCount_zero (s : ℕ) : aliveCount 0 s = if s = 0 then 1 else 0 := by
  rw [aliveCount]
  split_ifs with h
  · subst h; decide
  · simp [aliveB, oddCount, Ne.symm h]

lemma aliveCount_eq_zero {k s : ℕ} (hs : k < s) : aliveCount k s = 0 := by
  rw [aliveCount, card_eq_zero, filter_eq_empty_iff]
  intro r _ h
  have := oddCount_le k r
  omega

theorem aliveCount_eq_aliveRow : ∀ k s, aliveCount k s = (aliveRow k).getD s 0
  | 0, s => by
    rw [aliveCount_zero]
    rcases s with _ | s <;> simp [aliveRow]
  | k + 1, s => by
    rw [aliveCount_succ]
    simp only [aliveRow]
    rcases Nat.lt_or_ge s (k + 2) with hs | hs
    · rw [List.getD_eq_getElem _ _ (by simpa using hs)]
      simp only [List.getElem_map, List.getElem_range]
      rw [aliveCount_eq_aliveRow k s]
      split_ifs <;> try rfl
      rw [aliveCount_eq_aliveRow k (s - 1)]; rfl
    · rw [List.getD_eq_default _ _ (by simpa using hs), aliveCount_eq_zero (by omega)]
      have := aliveCount_eq_zero (k := k) (s := s - 1) (by omega)
      split_ifs <;> omega

/-- `#goodSet k + ∑_s aliveRow k s = 2^k`. -/
theorem goodSet_card_add (k : ℕ) :
    (goodSet k).card + ∑ s ∈ range (k + 1), (aliveRow k).getD s 0 = 2 ^ k := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := range (2 ^ k)) (fun r => r ∈ goodSet k)
  rw [card_range] at hsplit
  have hg : (range (2 ^ k)).filter (fun r => r ∈ goodSet k) = goodSet k := by
    ext r; simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(mem_filter.1 h).1 |> mem_range.1, h⟩⟩
  have ha : ((range (2 ^ k)).filter (fun r => r ∉ goodSet k)).card =
      ∑ s ∈ range (k + 1), aliveCount k s := by
    rw [card_eq_sum_card_fiberwise (f := fun r => oddCount k r) (t := range (k + 1))]
    · refine sum_congr rfl (fun s _ => ?_)
      rw [aliveCount, filter_filter]
      congr 1
      ext r
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨hr, h1, h2⟩; exact ⟨hr, (not_mem_goodSet hr).1 h1, h2⟩
      · rintro ⟨hr, h1, h2⟩; exact ⟨hr, (not_mem_goodSet hr).2 h1, h2⟩
    · intro r _; simp only [coe_range, Set.mem_Iio]; have := oddCount_le k r; omega
  rw [hg, ha] at hsplit
  rw [← hsplit]
  congr 1
  exact sum_congr rfl (fun s _ => (aliveCount_eq_aliveRow k s).symm)

theorem goodSet_card_ten : (goodSet 10).card = 960 := by
  have h := goodSet_card_add 10
  have h2 : ∑ s ∈ range (10 + 1), (aliveRow 10).getD s 0 = 64 := by decide +kernel
  omega

theorem goodSet_card_hundred : (goodSet 100).card = 2 ^ 100 - 302560669500543257546172187 := by
  have h := goodSet_card_add 100
  have h2 : ∑ s ∈ range (100 + 1), (aliveRow 100).getD s 0 = 302560669500543257546172187 := by
    decide +kernel
  omega

end Collatz
