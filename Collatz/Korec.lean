import Collatz.Terras

/-!
# Density form of Terras' theorem, and Korec's theorem

* `density_not_descends`: the proportion of `n < N` that never drop below `n` tends to `0`.
* `korec` (Korec 1994): for every `c > log 3 / log 4 ≈ 0.7925`, almost every `n` reaches a
  value below `n ^ c`.

Proof of `korec`. For `n` with `2^t ≤ n < 2^(t+1)`, write `s = oddCount t n`. Then
`2^t T^t(n) + 2^t ≤ 3^s n + 3^t` (`iterate_bound`), so `T^t(n) < 2·3^s + (3/2)^t`, which is
`< n^c` for large `t` as soon as `s < t (L+1) / (2L)` (`korec_real`). Since `n ↦ n - 2^t` is a
bijection onto the residues mod `2^t`, the remaining `n` are counted by the second moment
`∑_{r < 2^t} (2 s(r) - t)^2 = t 2^t` (`sum_sq`), giving at most `L^2 2^t / t` of them.
-/

namespace Collatz

open Finset

/-! ## Density form of Terras' theorem -/

open Classical in
theorem density_not_descends :
    Filter.Tendsto (fun N : ℕ => ((((range N).filter (fun n => ¬ Descends n)).card : ℕ) : ℝ) / N)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / ε)
  obtain ⟨N0, hN0⟩ := almost_all_descend q
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have h' : (q : ℝ) * (((range N).filter (fun n => ¬ Descends n)).card : ℕ) ≤ N := by
    exact_mod_cast hN0 N (le_of_max_le_left hN)
  have hq' : 2 < ε * q := by rw [div_lt_iff₀ hε] at hq; linarith
  have hc0 : (0 : ℝ) ≤ (((range N).filter (fun n => ¬ Descends n)).card : ℕ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h' hε.le, mul_le_mul_of_nonneg_right hq'.le hc0,
    mul_pos hε (by linarith : (0 : ℝ) < N)]

/-! ## Pairing residues mod `2^(k+1)` -/

lemma sum_pair {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ r ∈ range (2 ^ (k + 1)), f (oddCount (k + 1) r) =
      ∑ r ∈ range (2 ^ k), (f (oddCount k r) + f (oddCount k r + 1)) := by
  rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl (fun r _ => ?_)
  rw [oddCount_succ, oddCount_succ, iterate_pow_add,
    show 2 ^ k + r = 2 ^ k * 1 + r by ring, oddCount_affine k le_rfl]
  have h3 := three_pow_mod_two (oddCount k r)
  rcases Nat.mod_two_eq_zero_or_one (kstepT^[k] r) with h | h
  · have hx : (3 ^ oddCount k r + kstepT^[k] r) % 2 = 1 := by omega
    rw [h, hx, Nat.add_zero]
  · have hx : (3 ^ oddCount k r + kstepT^[k] r) % 2 = 0 := by omega
    rw [h, hx, add_comm]; rfl

/-- Second moment: the number of odd steps is concentrated around `k / 2`. -/
theorem sum_sq (k : ℕ) :
    ∑ r ∈ range (2 ^ k), ((2 * oddCount k r : ℤ) - (k : ℕ)) ^ 2 = (k : ℕ) * 2 ^ k := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
    have hp := sum_pair (fun s : ℕ => ((2 * s : ℤ) - ((k + 1 : ℕ) : ℤ)) ^ 2) k
    rw [hp]
    have e : ∀ r, ((2 * (oddCount k r : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) ^ 2 +
        ((2 * ((oddCount k r + 1 : ℕ) : ℤ)) - ((k + 1 : ℕ) : ℤ)) ^ 2 =
        2 * ((2 * oddCount k r : ℤ) - (k : ℕ)) ^ 2 + 2 := by
      intro r; push_cast; ring
    rw [sum_congr rfl (fun r _ => e r), sum_add_distrib, ← mul_sum, ih, sum_const, card_range]
    push_cast
    ring

/-- Residues mod `2^t` with too many odd steps: `s ≥ t (L+1) / (2L)`. -/
def korecBad (L t : ℕ) : Finset ℕ :=
  (range (2 ^ t)).filter (fun r => t * (L + 1) ≤ 2 * L * oddCount t r)

theorem korecBad_card (L t : ℕ) : (korecBad L t).card * t ≤ L ^ 2 * 2 ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have key : ((korecBad L t).card : ℤ) * (t : ℤ) ^ 2 ≤ (L : ℤ) ^ 2 * ((t : ℕ) * 2 ^ t) := by
    calc ((korecBad L t).card : ℤ) * (t : ℤ) ^ 2 = ∑ r ∈ korecBad L t, (t : ℤ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ korecBad L t, (L : ℤ) ^ 2 * ((2 * oddCount t r : ℤ) - (t : ℕ)) ^ 2 := by
          apply sum_le_sum
          intro r hr
          simp only [korecBad, mem_filter] at hr
          have h1 : (t : ℤ) * (L + 1) ≤ 2 * L * oddCount t r := by exact_mod_cast hr.2
          have h2 : (t : ℤ) ≤ L * ((2 * oddCount t r : ℤ) - t) := by linarith
          have h0 : (0 : ℤ) ≤ t := by positivity
          calc (t : ℤ) ^ 2 = t * t := sq _
            _ ≤ (L * ((2 * oddCount t r : ℤ) - t)) * (L * ((2 * oddCount t r : ℤ) - t)) :=
                mul_le_mul h2 h2 h0 (by linarith)
            _ = _ := by ring
      _ ≤ ∑ r ∈ range (2 ^ t), (L : ℤ) ^ 2 * ((2 * oddCount t r : ℤ) - (t : ℕ)) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = (L : ℤ) ^ 2 * ((t : ℕ) * 2 ^ t) := by rw [← mul_sum, sum_sq]
  have htz : (0 : ℤ) < t := by exact_mod_cast ht
  have e1 : ((korecBad L t).card : ℤ) * t * t = (korecBad L t).card * (t : ℤ) ^ 2 := by ring
  have e2 : (L : ℤ) ^ 2 * 2 ^ t * t = (L : ℤ) ^ 2 * ((t : ℕ) * 2 ^ t) := by ring
  have : ((korecBad L t).card : ℤ) * t ≤ (L : ℤ) ^ 2 * 2 ^ t :=
    le_of_mul_le_mul_right (by rw [e1, e2]; exact key) htz
  exact_mod_cast this

/-! ## Growth bound along the orbit -/

lemma iterate_bound (n : ℕ) :
    ∀ j, 2 ^ j * kstepT^[j] n + 2 ^ j ≤ 3 ^ oddCount j n * n + 3 ^ j
  | 0 => by simp [oddCount]
  | j + 1 => by
    have ih := iterate_bound n j
    have hpq : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
    rw [Function.iterate_succ_apply', oddCount_succ, pow_succ 2 j, pow_succ 3 j]
    generalize kstepT^[j] n = x at ih ⊢
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [h, Nat.add_zero, kstepT_of_even h]
      obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w := ⟨x / 2, by omega⟩
      rw [show 2 * w / 2 = w by omega]
      generalize 3 ^ oddCount j n * n = R at ih ⊢
      generalize 3 ^ j = Q at ih hpq ⊢
      generalize 2 ^ j = P at ih hpq ⊢
      nlinarith
    · rw [h, kstepT_of_odd h, pow_succ]
      obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w + 1 := ⟨x / 2, by omega⟩
      rw [show (3 * (2 * w + 1) + 1) / 2 = 3 * w + 2 by omega,
        show 3 ^ oddCount j n * 3 * n = 3 * (3 ^ oddCount j n * n) by ring]
      generalize 3 ^ oddCount j n * n = R at ih ⊢
      generalize 3 ^ j = Q at ih hpq ⊢
      generalize 2 ^ j = P at ih hpq ⊢
      nlinarith

/-! ## The real-number estimate -/

lemma korec_real {c : ℝ} (hc : Real.log 3 / Real.log 4 < c) :
    ∃ L : ℕ, 1 ≤ L ∧ ∃ t0 : ℕ, ∀ t ≥ t0, ∀ s : ℕ, 2 * L * s < t * (L + 1) →
      2 * (3 : ℝ) ^ s + (3 / 2 : ℝ) ^ t < (2 : ℝ) ^ (c * t) := by
  have hu : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have hvu : Real.log 3 < 2 * Real.log 2 := by
    rw [← h4]; exact Real.log_lt_log (by norm_num) (by norm_num)
  -- the gap G = c log 2 - log 3 / 2 > 0
  have hG : 0 < c * Real.log 2 - Real.log 3 / 2 := by
    rw [h4, div_lt_iff₀ (by positivity)] at hc; linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.log 3 / (c * Real.log 2 - Real.log 3 / 2))
  have hLG : Real.log 3 < L * (c * Real.log 2 - Real.log 3 / 2) := by
    rwa [div_lt_iff₀ hG] at hL
  have hLpos : (0 : ℝ) < L := by
    by_contra h0; push Not at h0
    have : (L : ℝ) * (c * Real.log 2 - Real.log 3 / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hG.le
    linarith
  obtain ⟨t0, ht0⟩ := exists_nat_gt (2 * Real.log 4 / (c * Real.log 2 - Real.log 3 / 2))
  refine ⟨L, by exact_mod_cast hLpos, t0, fun t ht s hs => ?_⟩
  have htg : 2 * Real.log 4 < t * (c * Real.log 2 - Real.log 3 / 2) := by
    rw [div_lt_iff₀ hG] at ht0
    have : (t0 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  have htpos : (0 : ℝ) ≤ t := by positivity
  have hsR : (2 * L * s : ℝ) < t * (L + 1) := by exact_mod_cast hs
  -- A: log 4 + s log 3 < log 2 * (c t)
  have hA : Real.log 4 + s * Real.log 3 < Real.log 2 * (c * t) := by
    have h1 := mul_lt_mul_of_pos_right hsR hv
    have h2 : (t : ℝ) * Real.log 3 ≤ t * (L * (c * Real.log 2 - Real.log 3 / 2)) :=
      mul_le_mul_of_nonneg_left hLG.le htpos
    have h3 : (L : ℝ) * (2 * Real.log 4) < L * (t * (c * Real.log 2 - Real.log 3 / 2)) :=
      mul_lt_mul_of_pos_left htg hLpos
    have key : (2 * L : ℝ) * (Real.log 4 + s * Real.log 3) < (2 * L) * (Real.log 2 * (c * t)) := by
      nlinarith
    exact lt_of_mul_lt_mul_left key (by positivity)
  -- B: log 2 + t log (3/2) < log 2 * (c t)
  have hB : Real.log 2 + t * Real.log (3 / 2) < Real.log 2 * (c * t) := by
    rw [h32]
    have h2 : (t : ℝ) * Real.log 3 ≤ t * (2 * Real.log 2) := mul_le_mul_of_nonneg_left hvu.le htpos
    nlinarith
  have hE : (2 : ℝ) ^ (c * t) = Real.exp (Real.log 2 * (c * t)) := Real.rpow_def_of_pos two_pos _
  have e1 : (4 : ℝ) * 3 ^ s = Real.exp (Real.log 4 + s * Real.log 3) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have e2 : (2 : ℝ) * (3 / 2) ^ t = Real.exp (Real.log 2 + t * Real.log (3 / 2)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have i1 := Real.exp_lt_exp.mpr hA
  have i2 := Real.exp_lt_exp.mpr hB
  rw [← e1, ← hE] at i1
  rw [← e2, ← hE] at i2
  linarith

/-- For `2^t ≤ n < 2^(t+1)` with few odd steps, `T^t n < n ^ c`. -/
lemma good_lt {c : ℝ} (hc0 : 0 ≤ c) {L t0 : ℕ}
    (H : ∀ t ≥ t0, ∀ s : ℕ, 2 * L * s < t * (L + 1) →
      2 * (3 : ℝ) ^ s + (3 / 2 : ℝ) ^ t < (2 : ℝ) ^ (c * t))
    {n t : ℕ} (ht : t0 ≤ t) (hn1 : 2 ^ t ≤ n) (hn2 : n < 2 ^ (t + 1))
    (hg : 2 * L * oddCount t n < t * (L + 1)) :
    ((kstepT^[t] n : ℕ) : ℝ) < (n : ℝ) ^ c := by
  have hb := iterate_bound n t
  have hbR : (2 : ℝ) ^ t * (kstepT^[t] n : ℕ) + 2 ^ t ≤ 3 ^ oddCount t n * n + 3 ^ t := by
    exact_mod_cast hb
  have hn2R : (n : ℝ) ≤ 2 ^ (t + 1) := by exact_mod_cast hn2.le
  have h3pos : (0 : ℝ) < 3 ^ oddCount t n := by positivity
  have h2pos : (0 : ℝ) < 2 ^ t := by positivity
  have hT : ((kstepT^[t] n : ℕ) : ℝ) < 2 * 3 ^ oddCount t n + (3 / 2) ^ t := by
    have e : (2 : ℝ) ^ t * (2 * 3 ^ oddCount t n + (3 / 2) ^ t) =
        3 ^ oddCount t n * 2 ^ (t + 1) + 3 ^ t := by
      rw [mul_add, ← mul_pow, pow_succ]; norm_num; ring
    have : (2 : ℝ) ^ t * (kstepT^[t] n : ℕ) < 2 ^ t * (2 * 3 ^ oddCount t n + (3 / 2) ^ t) := by
      rw [e]
      have := mul_le_mul_of_nonneg_left hn2R h3pos.le
      linarith
    exact lt_of_mul_lt_mul_left this h2pos.le
  have hpow : (2 : ℝ) ^ (c * t) ≤ (n : ℝ) ^ c := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn1) hc0
  exact hT.trans ((H t ht _ hg).trans_le hpow)

lemma sum_two_pow_lt : ∀ n : ℕ, ∑ i ∈ range n, 2 ^ i < 2 ^ n
  | 0 => by simp
  | n + 1 => by rw [sum_range_succ, pow_succ]; have := sum_two_pow_lt n; omega

/-! ## Korec's theorem -/

open Classical in
/-- **Korec's theorem.** For every `c > log 3 / log 4`, almost every `n` reaches a value
below `n ^ c`: for every `q`, at most `N / q` of the `n < N` stay `≥ n ^ c` forever. -/
theorem korec {c : ℝ} (hc : Real.log 3 / Real.log 4 < c) (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * ((range N).filter (fun n : ℕ => ∀ j, (n : ℝ) ^ c ≤ ((step^[j] n : ℕ) : ℝ))).card ≤ N := by
  obtain ⟨L, hL, t0, H⟩ := korec_real hc
  have hc0 : 0 ≤ c := le_trans (div_pos (Real.log_pos (by norm_num))
    (Real.log_pos (by norm_num))).le hc.le
  set t1 := max t0 (4 * q * L ^ 2 + 1)
  have ht1a : t0 ≤ t1 := le_max_left _ _
  have ht1b : 4 * q * L ^ 2 + 1 ≤ t1 := le_max_right _ _
  refine ⟨2 * q * 2 ^ t1 + 1, fun N hN => ?_⟩
  set T := Nat.log 2 N
  set U := (Ico t1 (T + 1)).biUnion (fun t => (korecBad L t).image (fun r => 2 ^ t + r))
  have hsub : (range N).filter (fun n : ℕ => ∀ j, (n : ℝ) ^ c ≤ ((step^[j] n : ℕ) : ℝ)) ⊆
      range (2 ^ t1) ∪ U := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    rw [mem_union, mem_range]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := t1); omega
    have ht1 : t1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h1
    have htT : Nat.log 2 n ≤ T := Nat.log_mono_right hn.1.le
    have hlo : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
    have hhi : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    set t := Nat.log 2 n
    have hr : n - 2 ^ t < 2 ^ t := by rw [pow_succ] at hhi; omega
    have hs : oddCount t n = oddCount t (n - 2 ^ t) := by
      have := oddCount_affine (k := t) (m := 1) (r := n - 2 ^ t) t le_rfl
      rwa [mul_one, Nat.add_sub_cancel' hlo] at this
    have hgood : 2 * L * oddCount t n < t * (L + 1) := by
      by_contra hb
      push Not at hb
      apply h2
      simp only [U, mem_biUnion, mem_Ico, mem_image, korecBad, mem_filter, mem_range]
      exact ⟨t, ⟨ht1, by omega⟩, n - 2 ^ t, ⟨hr, by rw [← hs]; exact hb⟩, by omega⟩
    have hlt := good_lt hc0 H (ht1a.trans ht1) hlo hhi hgood
    obtain ⟨j, -, hj⟩ := step_iterate_of_kstepT t n
    have := hn.2 j
    rw [hj] at this
    linarith
  have hN0 : N ≠ 0 := by omega
  have hU : U.card * t1 ≤ 2 * L ^ 2 * N := by
    calc U.card * t1
        ≤ (∑ t ∈ Ico t1 (T + 1), ((korecBad L t).image (fun r => 2 ^ t + r)).card) * t1 :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ ≤ (∑ t ∈ Ico t1 (T + 1), (korecBad L t).card) * t1 :=
          Nat.mul_le_mul_right _ (sum_le_sum fun t _ => card_image_le)
      _ = ∑ t ∈ Ico t1 (T + 1), (korecBad L t).card * t1 := sum_mul _ _ _
      _ ≤ ∑ t ∈ Ico t1 (T + 1), L ^ 2 * 2 ^ t := sum_le_sum fun t ht =>
          (Nat.mul_le_mul_left _ (mem_Ico.1 ht).1).trans (korecBad_card L t)
      _ ≤ ∑ t ∈ range (T + 1), L ^ 2 * 2 ^ t :=
          sum_le_sum_of_subset (fun x hx => by simp only [mem_Ico, mem_range] at hx ⊢; omega)
      _ = L ^ 2 * ∑ t ∈ range (T + 1), 2 ^ t := (mul_sum _ _ _).symm
      _ ≤ L ^ 2 * 2 ^ (T + 1) := Nat.mul_le_mul_left _ (sum_two_pow_lt _).le
      _ ≤ 2 * L ^ 2 * N := by
          rw [pow_succ]
          have := Nat.pow_log_le_self 2 hN0
          calc L ^ 2 * (2 ^ T * 2) = 2 * L ^ 2 * 2 ^ T := by ring
            _ ≤ 2 * L ^ 2 * N := Nat.mul_le_mul_left _ this
  have hU2 : 2 * q * U.card ≤ N := by
    have hpos : 0 < 2 * L ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 2 * q * U.card * (2 * L ^ 2) = U.card * (4 * q * L ^ 2) := by ring
      _ ≤ U.card * t1 := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 * L ^ 2 * N := hU
      _ = N * (2 * L ^ 2) := by ring
  have hC := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at hC
  set C := ((range N).filter (fun n : ℕ => ∀ j, (n : ℝ) ^ c ≤ ((step^[j] n : ℕ) : ℝ))).card
  have h1 : q * C ≤ q * 2 ^ t1 + q * U.card := by
    calc q * C ≤ q * (2 ^ t1 + U.card) := Nat.mul_le_mul_left _ hC
      _ = _ := by ring
  have h2 : 2 * (q * U.card) = 2 * q * U.card := by ring
  have h3 : 2 * (q * 2 ^ t1) = 2 * q * 2 ^ t1 := by ring
  omega

end Collatz
