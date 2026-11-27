import Collatz.Circuit

/-!
# `m`-cycles without Baker's theorem

An `m`-cycle of `T = kstepT` is a cycle whose parity sequence consists of `m` blocks
"`kᵢ` odd steps, then `lᵢ` even steps" (Simons and de Weger 2005 excluded `m ≤ 68` with Baker's
theorem). For a `T`-cycle `n = x₀, x₁, …, x_K = n` we count the blocks by their first elements,
the odd `x_{i+1}` with `x_i` even (`oddBlocks`).

With `a(y) = y + 1, b(y) = T y + 1` for odd `y` and `a(y) = y, b(y) = T y` for even `y`, every
step satisfies `2 b(y) = 3^(y mod 2) a(y)` (`two_mul_bT`), so `2^K ∏ b(xᵢ) = 3^k ∏ a(xᵢ)`.
Shifting the index, `a(x_{i+1})` and `b(x_i)` agree except at the end of an odd run
(`a = y < y + 1 = b`) and at the start `x` of an odd run (`a = x + 1`, `b = x`). Hence if all
elements are `≥ N`, `N^m 2^K ≤ (N + 1)^m 3^k` (`mcycle_size`): the block analogue of
`IsCircuit.size`, with `m ln(1 + 1/N)` in place of `ln(1 + 1/N)`.

With a Farey pair `a/b < log₂ 3 < c/d` as in `Collatz.Circuit` and `2^c / 3^d ≥ 1 + 1/M`,
`(1 + 1/M) > (1 + 1/N)^m` excludes every lattice point `s (c, d) - t (a, b)`, so `k ≥ b + d`
(`mcycle_k_ge_of_farey`). For `m ≥ 2` there is no closed form for `n`, so the lattice points
with small gap are not excluded by an integrality check as for circuits.
-/

namespace Collatz

open Finset

/-- Number of odd blocks of the `T`-orbit of `n` over `K` steps: indices `i < K` with
`T^i n` even and `T^(i+1) n` odd. For a `T`-cycle of length `K` this is the number `m` of
blocks of its parity sequence (cyclically). -/
def oddBlocks (K n : ℕ) : ℕ :=
  ((range K).filter (fun i => kstepT^[i] n % 2 = 0 ∧ kstepT^[i + 1] n % 2 = 1)).card

/-- `a(y)`: `y + 1` for odd `y`, `y` for even `y`. -/
def aT (y : ℕ) : ℕ := if y % 2 = 1 then y + 1 else y

/-- `b(y)`: `T y + 1` for odd `y`, `T y` for even `y`. -/
def bT (y : ℕ) : ℕ := if y % 2 = 1 then kstepT y + 1 else kstepT y

lemma two_mul_bT (y : ℕ) : 2 * bT y = 3 ^ (y % 2) * aT y := by
  unfold aT bT
  split_ifs with h
  · rw [kstepT_of_odd h, h]; omega
  · have h0 : y % 2 = 0 := by omega
    rw [kstepT_of_even h0, h0]; omega

/-- `2^K ∏ b(xᵢ) = 3^k ∏ a(xᵢ)` over the first `K` steps. -/
lemma prod_bT (n : ℕ) : ∀ K, 2 ^ K * ∏ i ∈ range K, bT (kstepT^[i] n)
    = 3 ^ oddCount K n * ∏ i ∈ range K, aT (kstepT^[i] n)
  | 0 => by simp [oddCount]
  | K + 1 => by
    rw [prod_range_succ, prod_range_succ, oddCount_succ, pow_add, pow_add]
    have ih := prod_bT n K
    have hs := two_mul_bT (kstepT^[K] n)
    calc 2 ^ K * 2 ^ 1 * ((∏ i ∈ range K, bT (kstepT^[i] n)) * bT (kstepT^[K] n))
        = (2 ^ K * ∏ i ∈ range K, bT (kstepT^[i] n)) * (2 * bT (kstepT^[K] n)) := by ring
      _ = (3 ^ oddCount K n * ∏ i ∈ range K, aT (kstepT^[i] n))
            * (3 ^ (kstepT^[K] n % 2) * aT (kstepT^[K] n)) := by rw [ih, hs]
      _ = _ := by ring

/-- Shifting a product around a `T`-cycle. -/
lemma prod_shift_kstepT {n K : ℕ} (h : kstepT^[K] n = n) (f : ℕ → ℕ) :
    ∏ i ∈ range K, f (kstepT^[i + 1] n) = ∏ i ∈ range K, f (kstepT^[i] n) := by
  rcases K with _ | q
  · simp
  · rw [prod_range_succ, prod_range_succ' (fun i => f (kstepT^[i] n)), h]
    simp

lemma kstepT_iterate_pos {n : ℕ} (hn : 1 ≤ n) : ∀ i, 1 ≤ kstepT^[i] n
  | 0 => by simpa using hn
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    have := kstepT_iterate_pos hn i
    rcases Nat.mod_two_eq_zero_or_one (kstepT^[i] n) with h | h
    · rw [kstepT_of_even h]; omega
    · rw [kstepT_of_odd h]; omega

/-- Per-step comparison of `a(x_{i+1})` with `b(x_i)`. -/
lemma aT_le_bT {N y : ℕ} (hN : N ≤ kstepT y) :
    (if y % 2 = 0 ∧ kstepT y % 2 = 1 then N else 1) * aT (kstepT y)
      ≤ (if y % 2 = 0 ∧ kstepT y % 2 = 1 then N + 1 else 1) * bT y := by
  unfold aT bT
  generalize hz : kstepT y = z at hN ⊢
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one z with h' | h'
  all_goals simp [h, h']
  nlinarith

/-- **Size bound for `m`-cycles.** If `T^K n = n` and all `T^i n ≥ N`, then
`N^m 2^K ≤ (N + 1)^m 3^k` with `m = oddBlocks K n`, `k = oddCount K n`. -/
theorem mcycle_size {N n K : ℕ} (hn : 1 ≤ n) (hper : kstepT^[K] n = n)
    (hbig : ∀ i, N ≤ kstepT^[i] n) :
    N ^ oddBlocks K n * 2 ^ K ≤ (N + 1) ^ oddBlocks K n * 3 ^ oddCount K n := by
  set m := oddBlocks K n
  set Pa := ∏ i ∈ range K, aT (kstepT^[i] n)
  set Pb := ∏ i ∈ range K, bT (kstepT^[i] n)
  have hid : 2 ^ K * Pb = 3 ^ oddCount K n * Pa := prod_bT n K
  have hPb : 0 < Pb := by
    refine prod_pos fun i _ => ?_
    have h1 := kstepT_iterate_pos hn i
    unfold bT
    split_ifs with h
    · omega
    · rw [kstepT_of_even (by omega)]; omega
  have hle : ∏ i ∈ range K, ((if kstepT^[i] n % 2 = 0 ∧ kstepT^[i + 1] n % 2 = 1 then N else 1)
        * aT (kstepT^[i + 1] n))
      ≤ ∏ i ∈ range K, ((if kstepT^[i] n % 2 = 0 ∧ kstepT^[i + 1] n % 2 = 1 then N + 1 else 1)
        * bT (kstepT^[i] n)) := by
    refine prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => ?_)
    have := hbig (i + 1)
    rw [Function.iterate_succ_apply'] at this ⊢
    exact aT_le_bT this
  rw [prod_mul_distrib, prod_mul_distrib, prod_ite, prod_ite, prod_shift_kstepT hper aT] at hle
  simp only [prod_const, one_pow, mul_one] at hle
  -- hle : N^m * Pa ≤ (N+1)^m * Pb
  have h2 : N ^ m * 2 ^ K * Pb ≤ (N + 1) ^ m * 3 ^ oddCount K n * Pb := by
    calc N ^ m * 2 ^ K * Pb = 3 ^ oddCount K n * (N ^ m * Pa) := by rw [mul_assoc, hid]; ring
      _ ≤ 3 ^ oddCount K n * ((N + 1) ^ m * Pb) := Nat.mul_le_mul_left _ hle
      _ = (N + 1) ^ m * 3 ^ oddCount K n * Pb := by ring
  exact Nat.le_of_mul_le_mul_right h2 hPb

/-- The lattice point `(K, k) = s (c, d) - t (a, b)` has `2^K / 3^k ≥ (2^c / 3^d)^s`. -/
lemma lattice_ge {a b c d k K s t M : ℕ} (hlow : 2 ^ a ≤ 3 ^ b)
    (hup : (M + 1) * 3 ^ d ≤ M * 2 ^ c) (hK : K + a * t = c * s) (hk : k + b * t = d * s) :
    (M + 1) ^ s * 3 ^ k ≤ M ^ s * 2 ^ K := by
  have h1 : ((M + 1) * 3 ^ d) ^ s ≤ (M * 2 ^ c) ^ s := Nat.pow_le_pow_left hup s
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← hK, ← hk, pow_add, pow_add] at h1
  have h2 : 2 ^ (a * t) ≤ 3 ^ (b * t) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left hlow t
  have h3 : (M + 1) ^ s * 3 ^ k * 2 ^ (a * t) ≤ M ^ s * 2 ^ K * 2 ^ (a * t) := by
    calc (M + 1) ^ s * 3 ^ k * 2 ^ (a * t) ≤ (M + 1) ^ s * 3 ^ k * 3 ^ (b * t) :=
          Nat.mul_le_mul_left _ h2
      _ = (M + 1) ^ s * (3 ^ k * 3 ^ (b * t)) := by ring
      _ ≤ M ^ s * (2 ^ K * 2 ^ (a * t)) := h1
      _ = M ^ s * 2 ^ K * 2 ^ (a * t) := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

/-- **Bounded `m`-cycle theorem.** Let `a/b < c/d` be adjacent Farey fractions with
`2^a < 3^b`, `2^c / 3^d ≥ 1 + 1/M` and `1 + 1/M > (1 + 1/N)^m`. Then a `T`-cycle of length `K`
with at most `m` odd blocks and all elements `≥ N` has at least `b + d` odd steps. -/
theorem mcycle_k_ge_of_farey {a b c d N M m n K : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hup : (M + 1) * 3 ^ d ≤ M * 2 ^ c)
    (hNM : (N + 1) ^ m * M < N ^ m * (M + 1)) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hbig : ∀ i, N ≤ kstepT^[i] n) (hm : oddBlocks K n ≤ m) :
    b + d ≤ oddCount K n := by
  set k := oddCount K n
  have hc := isCycle_of_kstepT_periodic hn hK hper
  have h3 : 3 ^ k < 2 ^ K := by
    have := three_pow_lt_two_pow hc
    rwa [card_odds_kstepT, card_evens_kstepT] at this
  have hk1 : 1 ≤ k := by
    have := Finset.card_pos.2 (odds_nonempty hc)
    rwa [card_odds_kstepT] at this
  -- size bound with `m` blocks
  have hsz : N ^ m * 2 ^ K ≤ (N + 1) ^ m * 3 ^ k := by
    have h0 := mcycle_size hn hper hbig
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hm
    rw [he, pow_add, pow_add]
    calc N ^ oddBlocks K n * N ^ e * 2 ^ K = N ^ e * (N ^ oddBlocks K n * 2 ^ K) := by ring
      _ ≤ (N + 1) ^ e * ((N + 1) ^ oddBlocks K n * 3 ^ k) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) e) h0
      _ = (N + 1) ^ oddBlocks K n * (N + 1) ^ e * 3 ^ k := by ring
  have hak := mul_lt_of_pow hk1 hlow h3
  rcases farey_or hdet hak with h | ⟨s, t, hs, hKs, hks⟩
  · exact h
  · exfalso
    have hM1 : 1 ≤ M := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0
        have : 0 < 3 ^ d := by positivity
        simp at hup
      · exact h0
    have hL := lattice_ge hlow.le hup hKs hks
    have h3k : 0 < 3 ^ k := by positivity
    -- N^m (M+1)^s ≤ (N+1)^m M^s
    have h5 : N ^ m * (M + 1) ^ s * 3 ^ k ≤ (N + 1) ^ m * M ^ s * 3 ^ k := by
      calc N ^ m * (M + 1) ^ s * 3 ^ k = N ^ m * ((M + 1) ^ s * 3 ^ k) := by ring
        _ ≤ N ^ m * (M ^ s * 2 ^ K) := Nat.mul_le_mul_left _ hL
        _ = M ^ s * (N ^ m * 2 ^ K) := by ring
        _ ≤ M ^ s * ((N + 1) ^ m * 3 ^ k) := Nat.mul_le_mul_left _ hsz
        _ = (N + 1) ^ m * M ^ s * 3 ^ k := by ring
    have h6 := Nat.le_of_mul_le_mul_right h5 h3k
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hMs : 0 < M ^ s' := by positivity
    have h7 : (N + 1) ^ m * M * M ^ s' < N ^ m * (M + 1) * M ^ s' :=
      Nat.mul_lt_mul_of_pos_right hNM hMs
    have h8 : N ^ m * (M + 1) * M ^ s' ≤ N ^ m * (M + 1) ^ (s' + 1) := by
      calc N ^ m * (M + 1) * M ^ s' = N ^ m * (M ^ s' * (M + 1)) := by ring
        _ ≤ N ^ m * ((M + 1) ^ s' * (M + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) s'))
        _ = N ^ m * (M + 1) ^ (s' + 1) := by ring
    have e1 : (N + 1) ^ m * M * M ^ s' = (N + 1) ^ m * M ^ (s' + 1) := by ring
    have h9 : (N + 1) ^ m * M ^ (s' + 1) < N ^ m * (M + 1) ^ (s' + 1) := e1 ▸ h7.trans_le h8
    exact (not_le.2 h9) h6

/-- **No nontrivial `m`-cycle below the Farey bound.** If every `1 ≤ y < N` reaches `1`, then a
`T`-cycle with at most `m` odd blocks and fewer than `b + d` odd steps consists of numbers
reaching `1`. -/
theorem reachesOne_of_mcycle {a b c d N M m n K : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hup : (M + 1) * 3 ^ d ≤ M * 2 ^ c)
    (hNM : (N + 1) ^ m * M < N ^ m * (M + 1))
    (hsmall : ∀ y, 1 ≤ y → y < N → ReachesOne y) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ m) (hk : oddCount K n < b + d) :
    ReachesOne n := by
  by_contra hr
  have hbig : ∀ i, N ≤ kstepT^[i] n := by
    intro i
    by_contra hlt
    have h1 := hsmall _ (kstepT_iterate_pos hn i) (by omega)
    rw [kstepT_iterate_eq_step] at h1
    exact hr (ReachesOne.of_iterate h1)
  have := mcycle_k_ge_of_farey hdet hlow hup hNM hn hK hper hbig hm
  omega

/-- A circuit has exactly one odd block. -/
theorem IsCircuit.oddBlocks_eq {n k l : ℕ} (hc : IsCircuit n k l) : oddBlocks (k + l) n = 1 := by
  obtain ⟨hk, hl, ho, he, hp⟩ := hc
  unfold oddBlocks
  rw [Finset.card_eq_one]
  refine ⟨k + l - 1, ?_⟩
  ext i
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hi, h0, h1⟩
    by_contra hne
    rcases Nat.lt_or_ge i k with hik | hik
    · have := ho i hik; omega
    · have := he (i - k) (by omega)
      rw [show k + (i - k) = i by omega] at this
      have h1' := he (i + 1 - k) (by omega)
      rw [show k + (i + 1 - k) = i + 1 by omega] at h1'
      omega
  · rintro rfl
    refine ⟨by omega, ?_, ?_⟩
    · have := he (l - 1) (by omega)
      rwa [show k + (l - 1) = k + l - 1 by omega] at this
    · rw [show k + l - 1 + 1 = k + l by omega, hp]
      simpa using ho 0 (by omega)

/-- With the verification of all `n < 1024` and the pair `84/53 < log₂ 3 < 401/253`: a `T`-cycle
with at most `3` odd blocks and fewer than `306` odd steps consists of numbers reaching `1`. -/
theorem reachesOne_of_mcycle_three {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 3) (hk : oddCount K n < 306) :
    ReachesOne n :=
  reachesOne_of_mcycle (a := 84) (b := 53) (c := 401) (d := 253) (N := 1024) (M := 322)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ h1 h2 => reachesOne_lt_1024 h1 h2) hn hK hper hm (by omega)

end Collatz
