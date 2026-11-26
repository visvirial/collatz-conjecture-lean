import Collatz.Kernel

/-!
# Cheap cycle exponent checks via rational bounds on `log₂ 3`

`cycleCheck` compares huge integers for every `b`, which is too slow for large `b`.
Here we instead use the rational bounds

  `176251 / 111202 < log₂ 3 < 301994 / 190537`

(convergents of `log₂ 3`, certified by the integer facts `2^176251 < 3^111202` and
`3^190537 < 2^301994`) together with `log (1 + x) ≤ x` and `log 2 > 0.6931471803`.
For a cycle with `a` even and `b` odd steps whose odd elements are `≥ N`:

* lower: `p b < a q`, so `a ≥ ⌊b p / q⌋ + 1`;
* upper: `a q' (3N) κd < b (p' (3N) κd + κn q')`, where `κn / κd > 1 / log 2`.

`cycCheck2 N b` checks that these are incompatible, using only small integers.
-/

namespace Collatz

/-- Lower convergent: `2^LP < 3^LQ`. -/
def LP : ℕ := 176251
def LQ : ℕ := 111202
/-- Upper convergent: `3^UQ < 2^UP`. -/
def UP : ℕ := 301994
def UQ : ℕ := 190537
/-- `κ = KN / KD > 1 / log 2`. -/
def KN : ℕ := 10000000000
def KD : ℕ := 6931471803

theorem lower_conv : 2 ^ LP < 3 ^ LQ := by decide +kernel
theorem upper_conv : 3 ^ UQ < 2 ^ UP := by decide +kernel

/-- From `3^b < 2^a`: `LP * b < a * LQ`. -/
lemma lower_exp {a b : ℕ} (hb : 1 ≤ b) (h : 3 ^ b < 2 ^ a) : LP * b < a * LQ := by
  have h1 : 2 ^ (LP * b) < 3 ^ (LQ * b) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left lower_conv (by omega)
  have h2 : 3 ^ (LQ * b) < 2 ^ (a * LQ) := by
    rw [mul_comm LQ b, pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left h (by norm_num [LQ])
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (h1.trans h2)

/-- From `N^b 2^a ≤ (3N+1)^b`: `a * UQ * (3N) * KD < b * (UP * (3N) * KD + KN * UQ)`. -/
lemma upper_exp {a b N : ℕ} (hb : 1 ≤ b) (hN : 1 ≤ N) (h : N ^ b * 2 ^ a ≤ (3 * N + 1) ^ b) :
    a * UQ * (3 * N) * KD < b * (UP * (3 * N) * KD + KN * UQ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKNr : (0 : ℝ) < KN := by norm_num [KN]
  have hKDr : (0 : ℝ) < KD := by norm_num [KD]
  have hUQr : (0 : ℝ) < UQ := by norm_num [UQ]
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  -- logarithmic form of the hypothesis
  have hR : (N : ℝ) ^ b * 2 ^ a ≤ (3 * N + 1) ^ b := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  -- log (3N+1) ≤ log 3 + log N + 1/(3N)
  have hD : Real.log (3 * N + 1) ≤ Real.log 3 + Real.log N + 1 / (3 * N) := by
    have e : (3 * N + 1 : ℝ) = (3 * N) * ((3 * N + 1) / (3 * N)) := by field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
      (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := (3 * N + 1) / (3 * N)) (by positivity)
    have e2 : (3 * N + 1 : ℝ) / (3 * N) - 1 = 1 / (3 * N) := by field_simp; ring
    linarith
  -- UQ log 3 < UP log 2
  have hU : (UQ : ℝ) * Real.log 3 < UP * Real.log 2 := by
    have h1 : (((3 ^ UQ : ℕ)) : ℝ) < (((2 ^ UP : ℕ)) : ℝ) := Nat.cast_lt.mpr upper_conv
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow, Nat.cast_ofNat,
      Nat.cast_ofNat] at h2
    exact h2
  have hL2 : (KD : ℝ) / KN < Real.log 2 := by
    have := Real.log_two_gt_d9
    rw [KD, KN]
    norm_num at this ⊢
    linarith
  have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- a log 2 ≤ b log 3 + b / (3N)
  have hA : (a : ℝ) * Real.log 2 ≤ b * Real.log 3 + b * (1 / (3 * N)) := by
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ b)
    nlinarith
  -- multiply by UQ * 3N:  X * log 2 < b * UQ, where X = a UQ 3N - b UP 3N
  set X : ℝ := a * UQ * (3 * N) - b * UP * (3 * N) with hX
  have h3N : (0 : ℝ) < 3 * N := by positivity
  have hXlt : X * Real.log 2 < b * UQ := by
    have e1 : (b : ℝ) * (1 / (3 * N)) * (UQ * (3 * N)) = b * UQ := by field_simp
    have h1 := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ UQ * (3 * N))
    have h2 : (b : ℝ) * Real.log 3 * (UQ * (3 * N)) < b * UP * (3 * N) * Real.log 2 := by
      have := mul_lt_mul_of_pos_left hU (by positivity : (0 : ℝ) < b * (3 * N))
      nlinarith
    rw [hX]
    nlinarith
  -- conclude X * KD < b * KN * UQ
  have hgoal : X * KD < b * KN * UQ := by
    rcases le_or_gt X 0 with hx | hx
    · have : (0 : ℝ) < b * KN * UQ := mul_pos (mul_pos (by linarith) hKNr) hUQr
      nlinarith
    · have hKN : (0 : ℝ) < KN := hKNr
      have : X * (KD / KN) < X * Real.log 2 := mul_lt_mul_of_pos_left hL2 hx
      have e : X * (KD / KN) * KN = X * KD := by field_simp
      nlinarith
  have : ((a * UQ * (3 * N) * KD : ℕ) : ℝ) < ((b * (UP * (3 * N) * KD + KN * UQ) : ℕ) : ℝ) := by
    push_cast
    rw [hX] at hgoal
    ring_nf at hgoal ⊢
    linarith
  exact_mod_cast this

/-- Cheap check that no cycle has `b` odd steps with all odd elements `≥ N`. -/
def cycCheck2 (N b : ℕ) : Bool :=
  b == 0 || Nat.ble (b * (UP * (3 * N) * KD + KN * UQ)) ((UQ * (3 * N) * KD) * (b * LP / LQ + 1))

theorem odds_card_ge_of_check2 {n p N B : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n)
    (hN : 1 ≤ N) (hsmall : ∀ y, 1 ≤ y → y < N → ReachesOne y)
    (hchk : kall (cycCheck2 N) B = true) : B ≤ (odds n p).card := by
  have hm : ∀ i ∈ odds n p, N ≤ step^[i] n := by
    intro i _
    by_contra hlt
    exact not_reachesOne_iterate hnr i (hsmall _ (iterate_pos hc.1 i) (by omega))
  have hb1 : 1 ≤ (odds n p).card := Finset.card_pos.2 (odds_nonempty hc)
  have hup := upper_exp hb1 hN (two_pow_le hc hm)
  have hlow := lower_exp hb1 (three_pow_lt_two_pow hc)
  by_contra hb
  have h1 := kall_spec hchk _ (by omega : (odds n p).card < B)
  unfold cycCheck2 at h1
  rw [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq] at h1
  rcases h1 with h0 | h1
  · omega
  · set a := (evens n p).card
    set b := (odds n p).card
    have ha : b * LP / LQ + 1 ≤ a := by
      have : b * LP / LQ < a := (Nat.div_lt_iff_lt_mul (by norm_num [LQ])).2 (by rw [mul_comm b LP]; exact hlow)
      omega
    have : UQ * (3 * N) * KD * (b * LP / LQ + 1) ≤ UQ * (3 * N) * KD * a :=
      Nat.mul_le_mul_left _ ha
    have e : a * UQ * (3 * N) * KD = UQ * (3 * N) * KD * a := by ring
    omega

end Collatz
