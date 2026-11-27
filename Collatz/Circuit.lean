import Collatz.NatCycles

/-!
# Circuits (Steiner's 1-cycles) without Baker's theorem

In the accelerated map `T = kstepT`, a *circuit* is a `T`-cycle made of `k ≥ 1` consecutive odd
steps followed by `l ≥ 1` consecutive even steps (Steiner 1977). Along the odd run
`2 (T x + 1) = 3 (x + 1)`, so with `K = k + l`

  `2^K n + 2^k = 3^k n + 3^k`,   i.e.   `n (2^K - 3^k) = 3^k - 2^k`   (`IsCircuit.identity`).

Hence `3^k < 2^K` and, if `n ≥ N`, `N 2^K < (N + 1) 3^k`: the fraction `K / k` lies just above
`log₂ 3`. Steiner excluded every nontrivial circuit with Baker's theorem. Here we only use
integer facts about one Farey pair `a / b < log₂ 3 < c / d` (`b c - a d = 1`, certified by
`2^a < 3^b` and `3^d < 2^c`):

* if `K / k < c / d` then `K / k` lies strictly between two adjacent Farey fractions, so
  `k ≥ b + d` (`farey_or`);
* otherwise `(K, k) = s (c, d) - t (a, b)` with `s ≥ 1, t ≥ 0`, so
  `2^K / 3^k ≥ (2^c / 3^d)^s`, which is too large for `n ≥ N` as soon as
  `2^c / 3^d ≥ 1 + 1 / M` with `M ≤ s N` (`size_excl`).

`circuit_k_ge_of_farey` is the plain version (`M = N`). `circuit_k_ge_of_farey'` allows
`M = 2 N`, which leaves the single lattice point `(K, k) = (c, d)`; it is excluded by checking
that `2^c - 3^d` does not divide `3^d - 2^d`. A lower convergent `a / b` with huge `b` is
obtained from smaller certified inequalities by `two_pow_lt_of_anchors`.

A circuit through a number that reaches `1` is the trivial one (`IsCircuit.eq_one_of_reachesOne`,
`isCircuit_one_iff`). With the verification of all `n < 1024` this gives
`no_circuit_lt_1636`; `CollatzBig.Circuit` uses the bound `7281311744` instead.
-/

namespace Collatz

/-- `n` starts a circuit: `k ≥ 1` odd `T`-steps followed by `l ≥ 1` even `T`-steps back to `n`. -/
def IsCircuit (n k l : ℕ) : Prop :=
  1 ≤ k ∧ 1 ≤ l ∧ (∀ i < k, kstepT^[i] n % 2 = 1) ∧ (∀ i < l, kstepT^[k + i] n % 2 = 0) ∧
    kstepT^[k + l] n = n

/-- Along a run of odd values, `2^k (T^k n + 1) = 3^k (n + 1)`. -/
lemma odd_run {n : ℕ} : ∀ k, (∀ i < k, kstepT^[i] n % 2 = 1) →
    2 ^ k * (kstepT^[k] n + 1) = 3 ^ k * (n + 1)
  | 0, _ => by simp
  | k + 1, h => by
    have ih := odd_run k (fun i hi => h i (by omega))
    have ho := h k (by omega)
    rw [Function.iterate_succ_apply', kstepT_of_odd ho]
    obtain ⟨y, hy⟩ : ∃ y, kstepT^[k] n = y := ⟨_, rfl⟩
    rw [hy] at ih ho ⊢
    have e : 2 * ((3 * y + 1) / 2 + 1) = 3 * (y + 1) := by omega
    calc 2 ^ (k + 1) * ((3 * y + 1) / 2 + 1) = 2 ^ k * (2 * ((3 * y + 1) / 2 + 1)) := by ring
      _ = 3 * (2 ^ k * (y + 1)) := by rw [e]; ring
      _ = 3 ^ (k + 1) * (n + 1) := by rw [ih]; ring

/-- Along a run of even values, `2^l T^l m = m`. -/
lemma even_run {m : ℕ} : ∀ l, (∀ i < l, kstepT^[i] m % 2 = 0) → 2 ^ l * kstepT^[l] m = m
  | 0, _ => by simp
  | l + 1, h => by
    have ih := even_run l (fun i hi => h i (by omega))
    have he := h l (by omega)
    rw [Function.iterate_succ_apply', kstepT_of_even he]
    obtain ⟨y, hy⟩ : ∃ y, kstepT^[l] m = y := ⟨_, rfl⟩
    rw [hy] at ih he ⊢
    rw [pow_succ, mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)]
    exact ih

namespace IsCircuit

variable {n k l : ℕ}

/-- **Circuit identity.** `2^(k+l) n + 2^k = 3^k n + 3^k`. -/
theorem identity (h : IsCircuit n k l) : 2 ^ (k + l) * n + 2 ^ k = 3 ^ k * n + 3 ^ k := by
  obtain ⟨-, -, ho, he, hp⟩ := h
  have h1 := odd_run k ho
  have h2 := even_run (m := kstepT^[k] n) l (fun i hi => by
    rw [← Function.iterate_add_apply, add_comm i k]
    exact he i hi)
  rw [← Function.iterate_add_apply, add_comm l k, hp] at h2
  rw [← h2] at h1
  calc 2 ^ (k + l) * n + 2 ^ k = 2 ^ k * (2 ^ l * n + 1) := by ring
    _ = 3 ^ k * (n + 1) := h1
    _ = 3 ^ k * n + 3 ^ k := by ring

lemma odd (h : IsCircuit n k l) : n % 2 = 1 := by
  simpa using h.2.2.1 0 (by have := h.1; omega)

lemma pos (h : IsCircuit n k l) : 1 ≤ n := by
  have := h.odd; omega

/-- `3^k < 2^(k+l)`. -/
lemma three_pow_lt (h : IsCircuit n k l) : 3 ^ k < 2 ^ (k + l) := by
  have e := h.identity
  have hn := h.pos
  have h23 : 2 ^ k < 3 ^ k := Nat.pow_lt_pow_left (by norm_num) (by have := h.1; omega)
  by_contra hle
  have : 2 ^ (k + l) * n ≤ 3 ^ k * n := Nat.mul_le_mul_right _ (by omega)
  omega

/-- If `n ≥ N` then `N 2^(k+l) < (N + 1) 3^k`. -/
lemma size {N : ℕ} (h : IsCircuit n k l) (hN : N ≤ n) : N * 2 ^ (k + l) < (N + 1) * 3 ^ k := by
  have e := h.identity
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_lt h.three_pow_lt
  rw [hD] at e ⊢
  have h2 : N * (D + 1) ≤ n * (D + 1) := Nat.mul_le_mul_right _ hN
  have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  nlinarith

/-- `2^(k+l) - 3^k` divides `3^k - 2^k` (the quotient is `n`). -/
lemma dvd (h : IsCircuit n k l) : 2 ^ (k + l) - 3 ^ k ∣ 3 ^ k - 2 ^ k := by
  have e := h.identity
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_lt h.three_pow_lt
  rw [hD] at e ⊢
  refine ⟨n, ?_⟩
  have h1 : 3 ^ k = 2 ^ k + (D + 1) * n := by nlinarith
  have h2 : 3 ^ k + D + 1 - 3 ^ k = D + 1 := by omega
  rw [h2, h1, Nat.add_sub_cancel_left]

end IsCircuit

/-! ### Farey pairs -/

/-- From `2^a < 3^b` and `3^k < 2^K`: `a k < K b`. -/
lemma mul_lt_of_pow {a b k K : ℕ} (hk : 1 ≤ k) (hlow : 2 ^ a < 3 ^ b) (h3 : 3 ^ k < 2 ^ K) :
    a * k < K * b := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hlow
  have h1 : 2 ^ (a * k) < 3 ^ (b * k) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left hlow (by omega)
  have h2 : 3 ^ (b * k) < 2 ^ (K * b) := by
    rw [mul_comm b k, pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left h3 hb
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (h1.trans h2)

/-- **Farey dichotomy.** If `a/b < K/k` with `b c - a d = 1`, then either `k ≥ b + d`, or
`(K, k) = s (c, d) - t (a, b)` with `s ≥ 1`, `t ≥ 0`. -/
lemma farey_or {a b c d k K : ℕ} (hdet : b * c = a * d + 1) (hak : a * k < K * b) :
    b + d ≤ k ∨ ∃ s t, 1 ≤ s ∧ K + a * t = c * s ∧ k + b * t = d * s := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt hak
  by_cases hkc : k * c ≤ K * d
  · right
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hkc
    refine ⟨s + 1, t, by omega, ?_, ?_⟩
    · have : (K : ℤ) + a * t = c * (s + 1) := by
        have hs' : (K : ℤ) * b = a * k + s + 1 := by exact_mod_cast hs
        have ht' : (K : ℤ) * d = k * c + t := by exact_mod_cast ht
        have hd' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
        linear_combination c * hs' - a * ht' - K * hd'
      exact_mod_cast this
    · have : (k : ℤ) + b * t = d * (s + 1) := by
        have hs' : (K : ℤ) * b = a * k + s + 1 := by exact_mod_cast hs
        have ht' : (K : ℤ) * d = k * c + t := by exact_mod_cast ht
        have hd' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
        linear_combination d * hs' - b * ht' - k * hd'
      exact_mod_cast this
  · left
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_lt (not_le.1 hkc)
    have e : (k : ℤ) = b * (u + 1) + d * (s + 1) := by
      have hs' : (K : ℤ) * b = a * k + s + 1 := by exact_mod_cast hs
      have hu' : (k : ℤ) * c = K * d + u + 1 := by exact_mod_cast hu
      have hd' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
      linear_combination b * hu' + d * hs' - k * hd'
    have e' : k = b * (u + 1) + d * (s + 1) := by exact_mod_cast e
    nlinarith

/-- Bernoulli's inequality: `M^s (M + s + 1) ≤ (M + 1)^(s + 1)`. -/
lemma bernoulli_nat (M : ℕ) : ∀ s, M ^ s * (M + s + 1) ≤ (M + 1) ^ (s + 1)
  | 0 => by simp
  | s + 1 => by
    have ih := bernoulli_nat M s
    have h1 : M * (M + (s + 1) + 1) ≤ (M + s + 1) * (M + 1) := by nlinarith
    calc M ^ (s + 1) * (M + (s + 1) + 1) = M ^ s * (M * (M + (s + 1) + 1)) := by ring
      _ ≤ M ^ s * ((M + s + 1) * (M + 1)) := Nat.mul_le_mul_left _ h1
      _ = M ^ s * (M + s + 1) * (M + 1) := by ring
      _ ≤ (M + 1) ^ (s + 1) * (M + 1) := Nat.mul_le_mul_right _ ih
      _ = (M + 1) ^ (s + 1 + 1) := by ring

/-- **Size exclusion.** If `2^c / 3^d ≥ 1 + 1/M` and `(K, k) = s (c, d) - t (a, b)` with
`2^a ≤ 3^b`, `s ≥ 1` and `M ≤ s N`, then `N 2^K < (N + 1) 3^k` is impossible. -/
lemma size_excl {a b c d k K s t N M : ℕ} (hlow : 2 ^ a ≤ 3 ^ b)
    (hup : (M + 1) * 3 ^ d ≤ M * 2 ^ c) (hs : 1 ≤ s) (hK : K + a * t = c * s)
    (hk : k + b * t = d * s) (hsz : N * 2 ^ K < (N + 1) * 3 ^ k) (hM : M ≤ s * N) : False := by
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0
      have : 0 < 3 ^ d := by positivity
      simp at hup
    · exact h0
  have h1 : ((M + 1) * 3 ^ d) ^ s ≤ (M * 2 ^ c) ^ s := Nat.pow_le_pow_left hup s
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← hK, ← hk, pow_add, pow_add] at h1
  have h2 : 2 ^ (a * t) ≤ 3 ^ (b * t) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left hlow t
  -- (M+1)^s 3^k ≤ M^s 2^K
  have h3 : (M + 1) ^ s * 3 ^ k * 2 ^ (a * t) ≤ M ^ s * 2 ^ K * 2 ^ (a * t) := by
    calc (M + 1) ^ s * 3 ^ k * 2 ^ (a * t) ≤ (M + 1) ^ s * 3 ^ k * 3 ^ (b * t) :=
          Nat.mul_le_mul_left _ h2
      _ = (M + 1) ^ s * (3 ^ k * 3 ^ (b * t)) := by ring
      _ ≤ M ^ s * (2 ^ K * 2 ^ (a * t)) := h1
      _ = M ^ s * 2 ^ K * 2 ^ (a * t) := by ring
  have h4 : (M + 1) ^ s * 3 ^ k ≤ M ^ s * 2 ^ K :=
    Nat.le_of_mul_le_mul_right h3 (by positivity)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hB := bernoulli_nat M s'
  have hMs : 0 < M ^ s' := by positivity
  have h3k : 0 < 3 ^ k := by positivity
  -- N (M+1)^s ≥ (N+1) M^s
  have h5 : M ^ (s' + 1) * (N + 1) ≤ N * (M + 1) ^ (s' + 1) := by
    have : M * (N + 1) ≤ N * (M + s' + 1) := by nlinarith
    calc M ^ (s' + 1) * (N + 1) = M ^ s' * (M * (N + 1)) := by ring
      _ ≤ M ^ s' * (N * (M + s' + 1)) := Nat.mul_le_mul_left _ this
      _ = N * (M ^ s' * (M + s' + 1)) := by ring
      _ ≤ N * (M + 1) ^ (s' + 1) := Nat.mul_le_mul_left _ hB
  have h6 : M ^ (s' + 1) * (N * 2 ^ K) < M ^ (s' + 1) * ((N + 1) * 3 ^ k) :=
    Nat.mul_lt_mul_of_pos_left hsz (by positivity)
  have h7 : N * ((M + 1) ^ (s' + 1) * 3 ^ k) ≤ N * (M ^ (s' + 1) * 2 ^ K) :=
    Nat.mul_le_mul_left _ h4
  have h8 : M ^ (s' + 1) * (N + 1) * 3 ^ k ≤ N * (M + 1) ^ (s' + 1) * 3 ^ k :=
    Nat.mul_le_mul_right _ h5
  have e1 : M ^ (s' + 1) * (N * 2 ^ K) = N * (M ^ (s' + 1) * 2 ^ K) := by ring
  have e2 : M ^ (s' + 1) * ((N + 1) * 3 ^ k) = M ^ (s' + 1) * (N + 1) * 3 ^ k := by ring
  have e3 : N * ((M + 1) ^ (s' + 1) * 3 ^ k) = N * (M + 1) ^ (s' + 1) * 3 ^ k := by ring
  omega

/-- **Bounded Steiner theorem, plain form.** Let `a/b < c/d` be adjacent Farey fractions
(`b c - a d = 1`) with `2^a < 3^b` and `2^c / 3^d ≥ 1 + 1/N`. Then every circuit with
`n ≥ N` has `k ≥ b + d` odd steps. -/
theorem circuit_k_ge_of_farey {a b c d N n k l : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hup : (N + 1) * 3 ^ d ≤ N * 2 ^ c) (hc : IsCircuit n k l)
    (hn : N ≤ n) : b + d ≤ k := by
  have hak := mul_lt_of_pow hc.1 hlow hc.three_pow_lt
  rcases farey_or hdet hak with h | ⟨s, t, hs, hK, hk⟩
  · exact h
  · exact (size_excl hlow.le hup hs hK hk (hc.size hn) (by nlinarith)).elim

/-- **Bounded Steiner theorem, refined form.** As `circuit_k_ge_of_farey`, but only
`2^c / 3^d ≥ 1 + 1/(2N)` is required, together with `d < b` and the non-integrality
`(2^c - 3^d) ∤ (3^d - 2^d)` of the only remaining candidate `(K, k) = (c, d)`. -/
theorem circuit_k_ge_of_farey' {a b c d N n k l : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hdb : d < b) (hup : (2 * N + 1) * 3 ^ d ≤ 2 * N * 2 ^ c)
    (hint : (3 ^ d - 2 ^ d) % (2 ^ c - 3 ^ d) ≠ 0) (hc : IsCircuit n k l) (hn : N ≤ n) :
    b + d ≤ k := by
  have hak := mul_lt_of_pow hc.1 hlow hc.three_pow_lt
  rcases farey_or hdet hak with h | ⟨s, t, hs, hK, hk⟩
  · exact h
  · rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · obtain rfl : s = 1 := by omega
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        simp only [mul_zero, add_zero, mul_one] at hK hk
        have hd := hc.dvd
        rw [hK, hk] at hd
        exact (hint (Nat.mod_eq_zero_of_dvd hd)).elim
      · have : b ≤ b * t := Nat.le_mul_of_pos_right b ht
        have := hc.1
        omega
    · exact (size_excl (M := 2 * N) hlow.le hup hs hK hk (hc.size hn)
        (Nat.mul_le_mul_right N hs2)).elim

/-- Lower bounds on `log₂ 3` from smaller certified ones: if `2^a / 3^b ≤ 1 - 1/R₁`,
`2^c / 3^d ≤ 1 + 1/R₂` and `(1 - 1/R₁)(1 + 1/R₂)^j < 1`, then `2^(a + j c) < 3^(b + j d)`. -/
lemma two_pow_lt_of_anchors {a b c d j R₁ R₂ : ℕ} (h1 : R₁ * 2 ^ a ≤ (R₁ - 1) * 3 ^ b)
    (h2 : R₂ * 2 ^ c ≤ (R₂ + 1) * 3 ^ d) (h3 : (R₁ - 1) * (R₂ + 1) ^ j < R₁ * R₂ ^ j) :
    2 ^ (a + j * c) < 3 ^ (b + j * d) := by
  have h2j : (R₂ * 2 ^ c) ^ j ≤ ((R₂ + 1) * 3 ^ d) ^ j := Nat.pow_le_pow_left h2 j
  have hm := Nat.mul_le_mul h1 h2j
  have e1 : R₁ * 2 ^ a * (R₂ * 2 ^ c) ^ j = (R₁ * R₂ ^ j) * 2 ^ (a + j * c) := by
    rw [mul_pow, pow_add, mul_comm j c, pow_mul]; ring
  have e2 : (R₁ - 1) * 3 ^ b * ((R₂ + 1) * 3 ^ d) ^ j
      = ((R₁ - 1) * (R₂ + 1) ^ j) * 3 ^ (b + j * d) := by
    rw [mul_pow, pow_add, mul_comm j d, pow_mul]; ring
  rw [e1, e2] at hm
  by_contra hge
  have h4 : (R₁ * R₂ ^ j) * 3 ^ (b + j * d) ≤ (R₁ * R₂ ^ j) * 2 ^ (a + j * c) :=
    Nat.mul_le_mul_left _ (not_lt.1 hge)
  have h5 : (R₁ * R₂ ^ j) * 3 ^ (b + j * d) < (R₁ * R₂ ^ j) * 3 ^ (b + j * d) :=
    lt_of_le_of_lt (h4.trans hm) (Nat.mul_lt_mul_of_pos_right h3 (by positivity))
  exact lt_irrefl _ h5

/-! ### Circuits through numbers that reach `1` -/

lemma step_iterate_one (i : ℕ) : step^[i] 1 = 1 ∨ step^[i] 1 = 2 ∨ step^[i] 1 = 4 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- A circuit through a number that reaches `1` starts at `1`. -/
theorem IsCircuit.eq_one_of_reachesOne {n k l : ℕ} (hc : IsCircuit n k l)
    (hr : ReachesOne n) : n = 1 := by
  obtain ⟨j, hj⟩ := hr
  have hP : step^[k + l + oddCount (k + l) n] n = n := by
    rw [← kstepT_iterate_eq_step, hc.2.2.2.2]
  have hper : Function.IsPeriodicPt step (k + l + oddCount (k + l) n) n := hP
  set P := k + l + oddCount (k + l) n
  have hP1 : 1 ≤ P := by have := hc.1; omega
  have hjP : step^[P * j] n = n := (hper.mul_const j).eq
  have e : P * j = (P * j - j) + j := by
    have : j ≤ P * j := Nat.le_mul_of_pos_left j hP1
    omega
  rw [e, Function.iterate_add_apply, hj] at hjP
  have ho := hc.odd
  rcases step_iterate_one (P * j - j) with h | h | h <;> rw [h] at hjP <;> omega

/-- The only circuit starting at `1` is `1 → 2 → 1`. -/
theorem isCircuit_one_iff {k l : ℕ} : IsCircuit 1 k l ↔ k = 1 ∧ l = 1 := by
  constructor
  · rintro ⟨hk, hl, ho, he, -⟩
    have hk1 : k = 1 := by
      by_contra h
      have := ho 1 (by omega)
      simp [kstepT] at this
    subst hk1
    refine ⟨rfl, ?_⟩
    by_contra h
    have := he 1 (by omega)
    simp [kstepT] at this
  · rintro ⟨rfl, rfl⟩
    refine ⟨le_rfl, le_rfl, fun i hi => ?_, fun i hi => ?_, by decide⟩
    · obtain rfl : i = 0 := by omega
      decide
    · obtain rfl : i = 0 := by omega
      decide

/-- **No nontrivial circuit below the Farey bound** (refined form): if every `1 ≤ y < N`
reaches `1`, then a circuit with fewer than `b + d` odd steps is `1 → 2 → 1`. -/
theorem no_circuit_of_farey' {a b c d N n k l : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hdb : d < b) (hup : (2 * N + 1) * 3 ^ d ≤ 2 * N * 2 ^ c)
    (hint : (3 ^ d - 2 ^ d) % (2 ^ c - 3 ^ d) ≠ 0)
    (hsmall : ∀ y, 1 ≤ y → y < N → ReachesOne y) (hc : IsCircuit n k l) (hk : k < b + d) :
    n = 1 ∧ k = 1 ∧ l = 1 := by
  have hn1 : n = 1 := by
    by_cases hr : ReachesOne n
    · exact hc.eq_one_of_reachesOne hr
    · have hn : N ≤ n := by
        by_contra hlt
        exact hr (hsmall n hc.pos (by omega))
      have := circuit_k_ge_of_farey' hdet hlow hdb hup hint hc hn
      omega
  subst hn1
  exact ⟨rfl, isCircuit_one_iff.1 hc⟩

/-- **No nontrivial circuit below the Farey bound** (plain form). -/
theorem no_circuit_of_farey {a b c d N n k l : ℕ} (hdet : b * c = a * d + 1)
    (hlow : 2 ^ a < 3 ^ b) (hup : (N + 1) * 3 ^ d ≤ N * 2 ^ c)
    (hsmall : ∀ y, 1 ≤ y → y < N → ReachesOne y) (hc : IsCircuit n k l) (hk : k < b + d) :
    n = 1 ∧ k = 1 ∧ l = 1 := by
  have hn1 : n = 1 := by
    by_cases hr : ReachesOne n
    · exact hc.eq_one_of_reachesOne hr
    · have hn : N ≤ n := by
        by_contra hlt
        exact hr (hsmall n hc.pos (by omega))
      have := circuit_k_ge_of_farey hdet hlow hup hc hn
      omega
  subst hn1
  exact ⟨rfl, isCircuit_one_iff.1 hc⟩

/-- With the verification of all `n < 1024` and the Farey pair `1054/665 < log₂ 3 < 1539/971`:
every circuit with fewer than `1636` odd steps is `1 → 2 → 1`. -/
theorem no_circuit_lt_1636 {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 1636) :
    n = 1 ∧ k = 1 ∧ l = 1 :=
  no_circuit_of_farey (a := 1054) (b := 665) (c := 1539) (d := 971) (N := 1024) (by norm_num)
    (by decide +kernel) (by decide +kernel) (fun _ h1 h2 => reachesOne_lt_1024 h1 h2) hc
    (by omega)

end Collatz
