import Collatz.CoeffStopDefs
import Collatz.StoppingTime
import Collatz.NatCycles
import Collatz.CycleBound

/-!
# Stopping time versus coefficient stopping time

Terras' coefficient stopping time conjecture says that every `n ≥ 2` first drops below itself
exactly when the coefficient `3^(s_j)/2^j` first drops below `1`. One direction always holds
(`stopsBy_imp`). For the other, if `n` has not dropped below itself in the first `j` steps then
`n^s 2^j ≤ (3n+1)^s` with `s = s_j(n)` (`pow_two_le_of_no_descent`), the same inequality as for a
cycle with odd elements `≥ n`; together with `3^s < 2^j` it is ruled out by `cycCheck2` once
`n` is large (`no_descent_contra`). `cst_of_tables` combines this with kernel checks for small
`n` and a bounded-descent verification for medium `n`; `CollatzBig.CoeffStop` instantiates it.
-/

namespace Collatz

open Finset

/-! ## The kernel check -/

lemma cstRun_spec (n : ℕ) : ∀ (fuel j : ℕ), (∀ i ≤ j, 2 ^ i ≤ 3 ^ oddCount i n) →
    cstRun n fuel (kstepT^[j] n) (3 ^ oddCount j n) (2 ^ j) = true →
    ∃ j0, j < j0 ∧ (∀ i < j0, 2 ^ i ≤ 3 ^ oddCount i n) ∧ 3 ^ oddCount j0 n < 2 ^ j0 ∧
      kstepT^[j0] n < n
  | 0, j, _, h => by simp [cstRun] at h
  | fuel + 1, j, halive, h => by
    have e3 : (bif kstepT^[j] n % 2 == 0 then 3 ^ oddCount j n else 3 * 3 ^ oddCount j n) =
        3 ^ oddCount (j + 1) n := by
      rw [oddCount_succ]
      rcases Nat.mod_two_eq_zero_or_one (kstepT^[j] n) with hp | hp <;> simp [hp, pow_succ, mul_comm]
    have e2 : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
    have ex : kstepT (kstepT^[j] n) = kstepT^[j + 1] n := (Function.iterate_succ_apply' _ _ _).symm
    simp only [cstRun] at h
    rw [e3, e2, ex] at h
    by_cases hc : 3 ^ oddCount (j + 1) n < 2 ^ (j + 1)
    · have hc' : (3 ^ oddCount (j + 1) n).blt (2 ^ (j + 1)) = true := by rw [Nat.blt_eq]; exact hc
      rw [hc', Bool.cond_true, Nat.blt_eq] at h
      exact ⟨j + 1, by omega, fun i hi => halive i (by omega), hc, h⟩
    · have hc' : (3 ^ oddCount (j + 1) n).blt (2 ^ (j + 1)) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hc
      rw [hc', Bool.cond_false] at h
      obtain ⟨j0, hj0, h1, h2, h3⟩ := cstRun_spec n fuel (j + 1) (fun i hi => by
        rcases Nat.lt_or_ge i (j + 1) with h' | h'
        · exact halive i (by omega)
        · rw [show i = j + 1 by omega]; omega) h
      exact ⟨j0, by omega, h1, h2, h3⟩

theorem cstCheck_spec {fuel n : ℕ} (hn : 2 ≤ n) (h : cstCheck fuel n = true) :
    ∃ j0, 0 < j0 ∧ (∀ i < j0, 2 ^ i ≤ 3 ^ oddCount i n) ∧ 3 ^ oddCount j0 n < 2 ^ j0 ∧
      kstepT^[j0] n < n := by
  unfold cstCheck at h
  rw [Bool.or_eq_true, Nat.blt_eq] at h
  rcases h with h | h
  · omega
  · exact cstRun_spec n fuel 0 (fun i hi => by simp [show i = 0 by omega, oddCount])
      (by simpa [oddCount] using h)

/-! ## No descent forces the cycle inequality -/

/-- If `n` has not dropped below itself in the first `j` steps, `2^j n^s ≤ (3n+1)^s`. -/
theorem pow_two_le_of_no_descent {n j : ℕ} (hn : 1 ≤ n)
    (h : ∀ i, 1 ≤ i → i ≤ j → n ≤ kstepT^[i] n) :
    2 ^ j * n ^ oddCount j n ≤ (3 * n + 1) ^ oddCount j n := by
  have key : ∀ i ≤ j, 2 ^ i * kstepT^[i] n * n ^ oddCount i n ≤ (3 * n + 1) ^ oddCount i n * n := by
    intro i
    induction i with
    | zero => intro; simp [oddCount]
    | succ i ih =>
      intro hi
      have ih := ih (by omega)
      have hx : n ≤ kstepT^[i] n := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · simp [h0]
        · exact h i h0 (by omega)
      rw [Function.iterate_succ_apply', oddCount_succ]
      generalize kstepT^[i] n = x at ih hx ⊢
      generalize oddCount i n = s at ih ⊢
      rcases Nat.mod_two_eq_zero_or_one x with hp | hp
      · rw [hp, Nat.add_zero, kstepT_of_even hp]
        have : 2 * (x / 2) = x := by omega
        calc 2 ^ (i + 1) * (x / 2) * n ^ s = 2 ^ i * (2 * (x / 2)) * n ^ s := by ring
          _ = 2 ^ i * x * n ^ s := by rw [this]
          _ ≤ _ := ih
      · rw [hp, kstepT_of_odd hp]
        have h2 : 2 * ((3 * x + 1) / 2) = 3 * x + 1 := by omega
        have h3 : (3 * x + 1) * n ≤ (3 * n + 1) * x := by nlinarith
        calc 2 ^ (i + 1) * ((3 * x + 1) / 2) * n ^ (s + 1)
            = 2 ^ i * (2 * ((3 * x + 1) / 2)) * (n ^ s * n) := by ring
          _ = 2 ^ i * n ^ s * ((3 * x + 1) * n) := by rw [h2]; ring
          _ ≤ 2 ^ i * n ^ s * ((3 * n + 1) * x) := Nat.mul_le_mul_left _ h3
          _ = (3 * n + 1) * (2 ^ i * x * n ^ s) := by ring
          _ ≤ (3 * n + 1) * ((3 * n + 1) ^ s * n) := Nat.mul_le_mul_left _ ih
          _ = (3 * n + 1) ^ (s + 1) * n := by ring
  have hk := key j le_rfl
  have hxj : n ≤ kstepT^[j] n := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · simp [h0]
    · exact h j h0 le_rfl
  have : 2 ^ j * n * n ^ oddCount j n ≤ (3 * n + 1) ^ oddCount j n * n :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxj)) hk
  have hn' : 0 < n := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hn'
  calc 2 ^ j * n ^ oddCount j n * n = 2 ^ j * n * n ^ oddCount j n := by ring
    _ ≤ _ := this

/-- The inequality transfers to any smaller `N ≥ 1`. -/
lemma pow_two_le_mono {N n j s : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n)
    (h : 2 ^ j * n ^ s ≤ (3 * n + 1) ^ s) : N ^ s * 2 ^ j ≤ (3 * N + 1) ^ s := by
  have h1 : (3 * n + 1) * N ≤ (3 * N + 1) * n := by nlinarith
  have h2 : ((3 * n + 1) * N) ^ s ≤ ((3 * N + 1) * n) ^ s := Nat.pow_le_pow_left h1 s
  rw [mul_pow, mul_pow] at h2
  have hpos : 0 < n ^ s := pow_pos (by omega) s
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc N ^ s * 2 ^ j * n ^ s = (2 ^ j * n ^ s) * N ^ s := by ring
    _ ≤ (3 * n + 1) ^ s * N ^ s := Nat.mul_le_mul_right _ h
    _ ≤ (3 * N + 1) ^ s * n ^ s := h2

/-- `cycCheck2` rules out the pair `(j, s)`. -/
theorem no_descent_contra {N B s j : ℕ} (hN : 1 ≤ N) (hchk : kall (cycCheck2 N) B = true)
    (hs : 1 ≤ s) (hsB : s < B) (h3 : 3 ^ s < 2 ^ j) (h : N ^ s * 2 ^ j ≤ (3 * N + 1) ^ s) :
    False := by
  have hup := upper_exp hs hN h
  have hlow := lower_exp hs h3
  have h1 := kall_spec hchk s hsB
  unfold cycCheck2 at h1
  rw [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq] at h1
  rcases h1 with h0 | h1
  · omega
  · have ha : s * LP / LQ + 1 ≤ j := by
      have : s * LP / LQ < j :=
        (Nat.div_lt_iff_lt_mul (by norm_num [LQ])).2 (by rw [mul_comm s LP]; exact hlow)
      omega
    have : UQ * (3 * N) * KD * (s * LP / LQ + 1) ≤ UQ * (3 * N) * KD * j :=
      Nat.mul_le_mul_left _ ha
    have e : j * UQ * (3 * N) * KD = UQ * (3 * N) * KD * j := by ring
    omega

/-! ## Bounded descent from the residue verification -/

/-- `kdesc` in units of accelerated steps, with the bound. -/
lemma kdesc_spec_T {n0 : ℕ} :
    ∀ {fuel x : ℕ}, kdesc n0 fuel x = true → ∃ i, 1 ≤ i ∧ i ≤ fuel ∧ kstepT^[i] x < n0
  | 0, x, h => by
    have : kdesc n0 0 x = false := rfl
    simp [this] at h
  | f + 1, x, h => by
    have e : kdesc n0 (f + 1) x = ((kstepT x).blt n0 || kdesc n0 f (kstepT x)) := rfl
    rw [e, Bool.or_eq_true, Nat.blt_eq] at h
    rcases h with h | h
    · exact ⟨1, le_rfl, by omega, by simpa using h⟩
    · obtain ⟨i, hi, hif, he⟩ := kdesc_spec_T h
      exact ⟨i + 1, by omega, by omega, by rw [Function.iterate_succ_apply]; exact he⟩

/-- `certAux` with the bound on the number of steps. -/
lemma certAux_spec_bounded {K r : ℕ} :
    ∀ {fuel a b : ℕ}, certAux K r fuel a b = true → ∀ m : ℕ,
      ∃ j a' b', 1 ≤ j ∧ j ≤ fuel ∧ a' < K ∧ b' ≤ r ∧ step^[j] (a * m + b) = a' * m + b'
  | 0, _, _, h, _ => by simp [certAux] at h
  | fuel + 1, a, b, h, m => by
    unfold certAux at h
    split_ifs at h with ha hc
    · exact ⟨1, _, _, le_rfl, by omega, hc.1, hc.2, by simpa using step_affine ha m⟩
    · obtain ⟨j, a', b', hj, hjf, ha', hb', he⟩ := certAux_spec_bounded h m
      refine ⟨j + 1, a', b', by omega, by omega, ha', hb', ?_⟩
      rw [Function.iterate_succ_apply, step_affine ha m, he]

/-- A drop below `n` after `j` Collatz steps is seen by `T` within `j` accelerated steps. -/
lemma kstepT_lt_of_step_lt {n j : ℕ} (h : step^[j] n < n) :
    ∃ i, 1 ≤ i ∧ i ≤ j ∧ kstepT^[i] n < n := by
  classical
  have hex : ∃ i, j < (i + 1) + oddCount (i + 1) n := ⟨j, by omega⟩
  set i0 := Nat.find hex
  have hi0 : j < (i0 + 1) + oddCount (i0 + 1) n := Nat.find_spec hex
  have hlo : i0 + oddCount i0 n ≤ j := by
    rcases Nat.eq_zero_or_pos i0 with h0 | h0
    · simp [h0, oddCount]
    · have := Nat.find_min hex (show i0 - 1 < i0 by omega)
      rw [show i0 - 1 + 1 = i0 by omega] at this
      omega
  rw [oddCount_succ] at hi0
  have hpar := Nat.mod_lt (kstepT^[i0] n) two_pos
  have hd : j - (i0 + oddCount i0 n) ≤ kstepT^[i0] n % 2 := by omega
  have hsplit : step^[j] n = step^[j - (i0 + oddCount i0 n)] (kstepT^[i0] n) := by
    rw [kstepT_iterate_eq_step n i0, ← Function.iterate_add_apply, Nat.sub_add_cancel hlo]
  rcases Nat.eq_zero_or_pos (j - (i0 + oddCount i0 n)) with hz | hz
  · rw [hsplit, hz, Function.iterate_zero_apply] at h
    have : 1 ≤ i0 := by
      rcases Nat.eq_zero_or_pos i0 with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    exact ⟨i0, this, by omega, h⟩
  · have hodd : kstepT^[i0] n % 2 = 1 := by omega
    have h1 : j - (i0 + oddCount i0 n) = 1 := by omega
    rw [hsplit, h1, Function.iterate_one, step_odd hodd] at h
    refine ⟨i0 + 1, by omega, by omega, ?_⟩
    rw [Function.iterate_succ_apply', kstepT_of_odd hodd]
    omega

/-- Bounded version of `descends_of_resCheck`, in accelerated steps. -/
theorem kstepT_descends_of_resCheck {k M fuel : ℕ} (h : ∀ r < 2 ^ k, resCheck k M fuel r = true) :
    ∀ n, 2 ≤ n → n < 2 ^ k * M → ∃ i, 1 ≤ i ∧ i ≤ max fuel (2 * k + 1) ∧ kstepT^[i] n < n := by
  intro n hn2 hnN
  have hK : 0 < 2 ^ k := by positivity
  set r := n % 2 ^ k with hr
  set m := n / 2 ^ k with hm
  have hnm : 2 ^ k * m + r = n := Nat.div_add_mod n (2 ^ k)
  have hmM : m < M := (Nat.div_lt_iff_lt_mul hK).2 (by rw [mul_comm]; exact hnN)
  have hrc := h r (Nat.mod_lt _ hK)
  unfold resCheck at hrc
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hrc
  rcases hrc with ⟨hc, hsmall⟩ | hall
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · have hnr : n = r := by rw [h0, mul_zero, zero_add] at hnm; exact hnm.symm
      rcases hsmall with hs | hs
      · omega
      · obtain ⟨i, hi, hif, he⟩ := kdesc_spec_T hs
        exact ⟨i, hi, le_trans hif (le_max_left _ _), by rw [hnr]; exact he⟩
    · obtain ⟨j, a', b', hj, hjf, ha', hb', he⟩ := certAux_spec_bounded hc m
      rw [hnm] at he
      have hlt : step^[j] n < n := by
        rw [he]
        have : a' * m < 2 ^ k * m := Nat.mul_lt_mul_of_pos_right ha' hpos
        omega
      obtain ⟨i, hi, hij, hT⟩ := kstepT_lt_of_step_lt hlt
      exact ⟨i, hi, le_trans hij (le_trans hjf (le_max_right _ _)), hT⟩
  · have := kall_spec hall m hmM
    rw [Bool.or_eq_true, Nat.blt_eq, hnm] at this
    rcases this with hs | hs
    · omega
    · obtain ⟨i, hi, hif, he⟩ := kdesc_spec_T hs
      exact ⟨i, hi, le_trans hif (le_max_left _ _), he⟩

/-! ## Combining the three ranges -/

/-- Generic form: kernel check below `N0`, bounded descent within `F` steps below `N1`,
and cycle-exponent checks at `N0` and `N1`. -/
theorem cst_of_tables {fuel F N0 N1 B0 B1 : ℕ} (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1)
    (hsmall : ∀ n, 2 ≤ n → n < N0 → cstCheck fuel n = true)
    (hmid : ∀ n, 2 ≤ n → n < N1 → ∃ i, 1 ≤ i ∧ i ≤ F ∧ kstepT^[i] n < n)
    (hc0 : kall (cycCheck2 N0) B0 = true) (hc1 : kall (cycCheck2 N1) B1 = true)
    (hF : ∀ s j, 3 ^ s < 2 ^ j → j < F → s < B0)
    {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) (h3 : 3 ^ oddCount j n < 2 ^ j)
    (hB1 : oddCount j n < B1) :
    ∃ i, 1 ≤ i ∧ i ≤ j ∧ kstepT^[i] n < n := by
  by_contra hno
  push Not at hno
  have hnd : ∀ i, 1 ≤ i → i ≤ j → n ≤ kstepT^[i] n := fun i h1 h2 => hno i h1 h2
  have hineq := pow_two_le_of_no_descent (by omega) hnd
  have hs1 : 1 ≤ oddCount j n := by
    by_contra h0
    push Not at h0
    have : oddCount j n = 0 := by omega
    rw [this, pow_zero, pow_zero, mul_one] at hineq
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  rcases Nat.lt_or_ge n N0 with h0 | h0
  · obtain ⟨j0, hj0, halive, hc, hd⟩ := cstCheck_spec hn (hsmall n hn h0)
    have hj0j : j0 ≤ j := by
      by_contra hgt
      push Not at hgt
      have := halive j hgt
      omega
    exact absurd hd (by have := hnd j0 hj0 hj0j; omega)
  rcases Nat.lt_or_ge n N1 with h1 | h1
  · obtain ⟨i, hi, hiF, hd⟩ := hmid n hn h1
    have hji : j < i := by
      by_contra hle
      push Not at hle
      have := hnd i hi hle
      omega
    exact no_descent_contra hN0 hc0 hs1 (hF _ _ h3 (by omega)) h3 (pow_two_le_mono hN0 h0 hineq)
  · exact no_descent_contra hN1 hc1 hs1 hB1 h3 (pow_two_le_mono hN1 h1 hineq)

end Collatz
