import Collatz.Kernel

/-!
# Terras' theorem: almost every integer descends

We work with the accelerated map `T = kstepT` (`n ↦ n / 2` or `(3n + 1) / 2`).

* `iterate_affine`: for `j ≤ k`, `T^j (2^k m + r) = 2^(k-j) 3^(s_j r) m + T^j r`, where
  `s_j r = oddCount j r` is the number of odd values among `r, T r, …, T^(j-1) r`.
* `parity_bijective` (Terras, Everett): the first `k` parities of `T`-orbits induce a
  bijection between residues mod `2^k` and parity vectors of length `k`.
* `sum_weight`: `∑_{r < 2^k} a^(s_k r) b^(k - s_k r) = (a + b)^k`.
* If `3^(s_k r) < 2^k`, every large `n ≡ r (mod 2^k)` descends. The residues with
  `2^k ≤ 3^(s_k r)` are few: with `a = 7, b = 4` and `k = 2j` their number `B` satisfies
  `B * 32^j ≤ 121^j`, i.e. a proportion at most `(121/128)^j`.
* `almost_all_descend`: for every `q`, eventually `q * #{n < N | ¬ Descends n} ≤ N`,
  i.e. the set of integers that never drop below their starting value has density `0`.
-/

namespace Collatz

open Finset

lemma kstepT_of_even {x : ℕ} (h : x % 2 = 0) : kstepT x = x / 2 := by
  simp [kstepT, h]

lemma kstepT_of_odd {x : ℕ} (h : x % 2 = 1) : kstepT x = (3 * x + 1) / 2 := by
  simp [kstepT, h]

/-- Number of odd values among the first `j` points `r, T r, …, T^(j-1) r`. -/
def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, r => oddCount j r + kstepT^[j] r % 2

lemma oddCount_succ (j r : ℕ) : oddCount (j + 1) r = oddCount j r + kstepT^[j] r % 2 := rfl

lemma oddCount_le (j r : ℕ) : oddCount j r ≤ j := by
  induction j with
  | zero => simp [oddCount]
  | succ j ih => rw [oddCount_succ]; have := Nat.mod_lt (kstepT^[j] r) two_pos; omega

/-- The orbit of `2^k m + r` is affine in `m` for the first `k` steps. -/
lemma iterate_affine {k m r : ℕ} :
    ∀ j ≤ k, kstepT^[j] (2 ^ k * m + r) = 2 ^ (k - j) * 3 ^ oddCount j r * m + kstepT^[j] r := by
  intro j
  induction j with
  | zero => intro; simp [oddCount]
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
      oddCount_succ]
    obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
    rw [he, show k - (j + 1) = e by omega]
    generalize kstepT^[j] r = y
    generalize oddCount j r = s
    have key : 2 ^ (e + 1) * 3 ^ s * m = 2 * (2 ^ e * 3 ^ s * m) := by ring
    rw [key]
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · rw [h, Nat.add_zero]
      generalize 2 ^ e * 3 ^ s * m = A
      rw [kstepT_of_even h, kstepT_of_even (by omega)]
      omega
    · have key3 : 2 ^ e * 3 ^ (s + 1) * m = 3 * (2 ^ e * 3 ^ s * m) := by ring
      rw [h, key3]
      generalize 2 ^ e * 3 ^ s * m = A
      rw [kstepT_of_odd h, kstepT_of_odd (by omega)]
      omega

/-- The first `k` parities of `2^k m + r` are those of `r`. -/
lemma parity_affine {k m r j : ℕ} (hj : j < k) :
    kstepT^[j] (2 ^ k * m + r) % 2 = kstepT^[j] r % 2 := by
  rw [iterate_affine j hj.le]
  obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
  rw [he, show 2 ^ (e + 1) * 3 ^ oddCount j r * m = 2 * (2 ^ e * 3 ^ oddCount j r * m) by ring]
  omega

lemma oddCount_affine {k m r : ℕ} : ∀ j ≤ k, oddCount j (2 ^ k * m + r) = oddCount j r := by
  intro j
  induction j with
  | zero => intro; rfl
  | succ j ih =>
    intro hj
    rw [oddCount_succ, oddCount_succ, ih (by omega), parity_affine (by omega)]

lemma three_pow_mod_two (s : ℕ) : 3 ^ s % 2 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- At step `k`, the parities of `r` and `2^k + r` differ. -/
lemma iterate_pow_add (k r : ℕ) : kstepT^[k] (2 ^ k + r) = 3 ^ oddCount k r + kstepT^[k] r := by
  have := iterate_affine (k := k) (m := 1) (r := r) k le_rfl
  simpa using this

/-! ## The parity vector bijection -/

/-- Residues `r, r' < 2^k` with the same first `k` parities are equal. -/
theorem parity_inj : ∀ {k r r' : ℕ}, r < 2 ^ k → r' < 2 ^ k →
    (∀ i < k, kstepT^[i] r % 2 = kstepT^[i] r' % 2) → r = r'
  | 0, r, r', hr, hr', _ => by simp at hr hr'; omega
  | k + 1, r, r', hr, hr', h => by
    set r0 := r % 2 ^ k
    set r0' := r' % 2 ^ k
    have hK : 0 < 2 ^ k := by positivity
    have e1 : 2 ^ k * (r / 2 ^ k) + r0 = r := Nat.div_add_mod r (2 ^ k)
    have e2 : 2 ^ k * (r' / 2 ^ k) + r0' = r' := Nat.div_add_mod r' (2 ^ k)
    have ha : r / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact hr)
    have ha' : r' / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact hr')
    have h0 : r0 = r0' := by
      refine parity_inj (Nat.mod_lt _ hK) (Nat.mod_lt _ hK) (fun i hi => ?_)
      have := h i (by omega)
      rw [← e1, ← e2, parity_affine hi, parity_affine hi] at this
      exact this
    have hk := h k (by omega)
    rw [← e1, ← e2, iterate_affine k le_rfl, iterate_affine k le_rfl, ← h0] at hk
    simp only [Nat.sub_self, pow_zero, one_mul] at hk
    have h3 := three_pow_mod_two (oddCount k r0)
    have hq : r / 2 ^ k = r' / 2 ^ k := by
      generalize r / 2 ^ k = a at ha hk
      generalize r' / 2 ^ k = a' at ha' hk
      generalize 3 ^ oddCount k r0 = t at hk h3
      generalize kstepT^[k] r0 = y at hk
      interval_cases a <;> interval_cases a' <;> omega
    rw [← e1, ← e2, hq, h0]

/-- Terras / Everett: parity vectors of length `k` correspond bijectively to residues
mod `2^k`. -/
theorem parity_bijective (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => fun i : Fin k => decide (kstepT^[i] r % 2 = 1)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r r' h => Fin.ext (parity_inj r.2 r'.2 (fun i hi => ?_)), by simp⟩
  have := congrFun h ⟨i, hi⟩
  simp only [decide_eq_decide] at this
  have := Nat.mod_two_eq_zero_or_one (kstepT^[i] r)
  have := Nat.mod_two_eq_zero_or_one (kstepT^[i] r')
  omega

/-! ## Counting residues by their number of odd steps -/

/-- Residues `r` and `2^k + r` share their first `k` parities and differ at step `k`. -/
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

theorem sum_weight (a b : ℕ) : ∀ k : ℕ,
    ∑ r ∈ range (2 ^ k), a ^ oddCount k r * b ^ (k - oddCount k r) = (a + b) ^ k
  | 0 => by simp [oddCount]
  | k + 1 => by
    rw [sum_pair (fun s => a ^ s * b ^ (k + 1 - s)) k, pow_succ, ← sum_weight a b k, sum_mul]
    refine sum_congr rfl (fun r _ => ?_)
    have hs := oddCount_le k r
    obtain ⟨t, ht⟩ : ∃ t, k - oddCount k r = t := ⟨_, rfl⟩
    rw [ht, show k + 1 - oddCount k r = t + 1 by omega,
      show k + 1 - (oddCount k r + 1) = t by omega]
    ring

/-- Residues mod `2^k` whose first `k` steps do not shrink the coefficient. -/
def badSet (k : ℕ) : Finset ℕ := (range (2 ^ k)).filter (fun r => 2 ^ k ≤ 3 ^ oddCount k r)

lemma term_bound {j s : ℕ} (hs : s ≤ 2 * j) (h : 2 ^ (2 * j) ≤ 3 ^ s) :
    2 ^ j * 4 ^ (2 * j) ≤ 7 ^ s * 4 ^ (2 * j - s) := by
  have h1 : 2 ^ j * 4 ^ s ≤ 7 ^ s := by
    have : (2 ^ j * 4 ^ s) ^ 2 ≤ (7 ^ s) ^ 2 := by
      calc (2 ^ j * 4 ^ s) ^ 2 = 2 ^ (2 * j) * 16 ^ s := by
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2, mul_comm s 2, pow_mul 4 2 s]
            norm_num
        _ ≤ 3 ^ s * 16 ^ s := Nat.mul_le_mul_right _ h
        _ = (3 * 16) ^ s := (mul_pow 3 16 s).symm
        _ ≤ 49 ^ s := Nat.pow_le_pow_left (by norm_num) s
        _ = (7 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  calc 2 ^ j * 4 ^ (2 * j) = 2 ^ j * 4 ^ s * 4 ^ (2 * j - s) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hs]
    _ ≤ 7 ^ s * 4 ^ (2 * j - s) := Nat.mul_le_mul_right _ h1

/-- At most a proportion `(121/128)^j` of the residues mod `2^(2j)` is bad. -/
theorem badSet_card (j : ℕ) : (badSet (2 * j)).card * (2 ^ j * 4 ^ (2 * j)) ≤ 121 ^ j := by
  calc (badSet (2 * j)).card * (2 ^ j * 4 ^ (2 * j))
      = (badSet (2 * j)).card • (2 ^ j * 4 ^ (2 * j)) := by rw [smul_eq_mul]
    _ ≤ ∑ r ∈ badSet (2 * j), 7 ^ oddCount (2 * j) r * 4 ^ (2 * j - oddCount (2 * j) r) := by
        apply card_nsmul_le_sum
        intro r hr
        simp only [badSet, mem_filter] at hr
        exact term_bound (oddCount_le _ _) hr.2
    _ ≤ ∑ r ∈ range (2 ^ (2 * j)), 7 ^ oddCount (2 * j) r * 4 ^ (2 * j - oddCount (2 * j) r) :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = 121 ^ j := by rw [sum_weight]; rw [pow_mul]; norm_num

/-! ## Descent of good residue classes -/

lemma kstepT_le (x : ℕ) : kstepT x ≤ 2 * x := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [kstepT_of_even h]; omega
  · rw [kstepT_of_odd h]; omega

lemma iterate_kstepT_le (x : ℕ) : ∀ k, kstepT^[k] x ≤ 2 ^ k * x
  | 0 => by simp
  | k + 1 => by
    rw [Function.iterate_succ_apply', pow_succ]
    have := iterate_kstepT_le x k
    have := kstepT_le (kstepT^[k] x)
    nlinarith

lemma step_iterate_of_kstepT : ∀ (k x : ℕ), ∃ j, k ≤ j ∧ step^[j] x = kstepT^[k] x
  | 0, x => ⟨0, le_rfl, rfl⟩
  | k + 1, x => by
    obtain ⟨i, hi, hix⟩ := kstepT_iter x
    obtain ⟨j, hj, hjx⟩ := step_iterate_of_kstepT k (kstepT x)
    refine ⟨j + i, by omega, ?_⟩
    rw [Function.iterate_add_apply, hix, hjx, Function.iterate_succ_apply]

/-- If the residue class of `n` mod `2^k` is good and `n ≥ 8^k`, then `n` descends. -/
theorem descends_of_good {k n : ℕ} (hg : 3 ^ oddCount k (n % 2 ^ k) < 2 ^ k) (hn : 8 ^ k ≤ n) :
    Descends n := by
  set r := n % 2 ^ k
  set m := n / 2 ^ k
  have hK : 0 < 2 ^ k := by positivity
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hg
    · exact h
  have e : 2 ^ k * m + r = n := Nat.div_add_mod n (2 ^ k)
  have hm : 4 ^ k ≤ m := by
    rw [Nat.le_div_iff_mul_le hK]
    calc 4 ^ k * 2 ^ k = 8 ^ k := by rw [← mul_pow]; norm_num
      _ ≤ n := hn
  have hr : r < 2 ^ k := Nat.mod_lt _ hK
  have hy : kstepT^[k] r < 4 ^ k := by
    calc kstepT^[k] r ≤ 2 ^ k * r := iterate_kstepT_le r k
      _ < 2 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_left hr hK
      _ = 4 ^ k := by rw [← mul_pow]; norm_num
  have hT := iterate_affine (k := k) (m := m) (r := r) k le_rfl
  simp only [Nat.sub_self, pow_zero, one_mul] at hT
  have hc : (3 ^ oddCount k r + 1) * m ≤ 2 ^ k * m := Nat.mul_le_mul_right m hg
  obtain ⟨j, hj, hjx⟩ := step_iterate_of_kstepT k n
  refine ⟨j, by omega, ?_⟩
  rw [hjx, ← e, hT]
  rw [add_mul, one_mul] at hc
  omega

/-! ## Density -/

lemma card_filter_mod_le (q N : ℕ) (_hq : 0 < q) (S : Finset ℕ) :
    ((range N).filter (fun n => n % q ∈ S)).card ≤ S.card * (N / q + 1) := by
  rw [← card_range (N / q + 1), ← card_product]
  apply card_le_card_of_injOn (fun n => (n % q, n / q))
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe]
    exact ⟨hn.2, Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    rw [← Nat.div_add_mod a q, ← Nat.div_add_mod b q, h.1, h.2]

lemma pow_bernoulli (j : ℕ) : 121 ^ j * (121 + 7 * j) ≤ 121 * 128 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 121 ^ j ≤ 128 ^ j := Nat.pow_le_pow_left (by norm_num) j
    calc 121 ^ (j + 1) * (121 + 7 * (j + 1))
        = 121 * (121 ^ j * (121 + 7 * j)) + 7 * 121 * 121 ^ j := by ring
      _ ≤ 121 * (121 * 128 ^ j) + 7 * 121 * 128 ^ j := by gcongr
      _ = 121 * 128 ^ (j + 1) := by ring

lemma pow128 (j : ℕ) : 128 ^ j = 2 ^ (2 * j) * (2 ^ j * 4 ^ (2 * j)) := by
  rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow]; norm_num

open Classical in
/-- **Terras' theorem.** Almost every positive integer eventually drops below itself:
for every `q`, at most `N / q` of the integers below `N` fail to descend, for `N` large. -/
theorem almost_all_descend (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * ((range N).filter (fun n => ¬ Descends n)).card ≤ N := by
  classical
  set j := 35 * q
  set k := 2 * j
  set B := (badSet k).card
  -- the bad proportion is at most 1 / (2q)
  have hB : 2 * q * B ≤ 2 ^ k := by
    have h1 := badSet_card j
    have h2 := pow_bernoulli j
    have h3 : 2 * q * 121 ≤ 121 + 7 * j := by omega
    have h4 : 2 * q * 121 ^ j * 121 ≤ 121 * 128 ^ j := by
      calc 2 * q * 121 ^ j * 121 = 121 ^ j * (2 * q * 121) := by ring
        _ ≤ 121 ^ j * (121 + 7 * j) := Nat.mul_le_mul_left _ h3
        _ ≤ 121 * 128 ^ j := h2
    have h5 : 2 * q * 121 ^ j ≤ 128 ^ j := by omega
    have e1 : 128 ^ j = 2 ^ k * (2 ^ j * 4 ^ (2 * j)) := pow128 j
    have hpos : 0 < 2 ^ j * 4 ^ (2 * j) := by positivity
    have : 2 * q * B * (2 ^ j * 4 ^ (2 * j)) ≤ 2 ^ k * (2 ^ j * 4 ^ (2 * j)) := by
      calc 2 * q * B * (2 ^ j * 4 ^ (2 * j)) = 2 * q * (B * (2 ^ j * 4 ^ (2 * j))) := by ring
        _ ≤ 2 * q * 121 ^ j := Nat.mul_le_mul_left _ h1
        _ ≤ 128 ^ j := h5
        _ = _ := e1
    exact Nat.le_of_mul_le_mul_right this hpos
  refine ⟨2 * (q * (8 ^ k + B)), fun N hN => ?_⟩
  have hK : 0 < 2 ^ k := by positivity
  -- non-descending integers are small or lie in a bad class
  have hsub : (range N).filter (fun n => ¬ Descends n) ⊆
      range (8 ^ k) ∪ (range N).filter (fun n => n % 2 ^ k ∈ badSet k) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [mem_union, mem_range, mem_filter, badSet]
    by_contra hc
    push Not at hc
    exact hn.2 (descends_of_good (by
      have := hc.2 hn.1 (Nat.mod_lt _ hK); omega) hc.1)
  have hC := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at hC
  have hF := card_filter_mod_le (2 ^ k) N hK (badSet k)
  set C := ((range N).filter (fun n => ¬ Descends n)).card
  set X := N / 2 ^ k
  have hX : 2 ^ k * X ≤ N := Nat.mul_div_le N (2 ^ k)
  have h1 : 2 * q * B * X ≤ N := (Nat.mul_le_mul_right X hB).trans hX
  have hC' : C ≤ 8 ^ k + B * (X + 1) := le_trans hC (Nat.add_le_add_left hF _)
  have h2 : q * C ≤ q * (8 ^ k + B) + q * B * X := by
    calc q * C ≤ q * (8 ^ k + B * (X + 1)) := Nat.mul_le_mul_left _ hC'
      _ = q * (8 ^ k + B) + q * B * X := by ring
  have h3 : 2 * (q * B * X) = 2 * q * B * X := by ring
  omega

end Collatz
