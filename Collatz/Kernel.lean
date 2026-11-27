import Collatz.Cycle

/-!
# Kernel-friendly verification

Checkers written with `Nat.rec` and `Bool` operations so that `decide +kernel` can evaluate
them efficiently (the kernel has GMP-accelerated `Nat` literals). Each checker is proved
sound, so large verifications can be split into many small kernel-checked chunk theorems.

* `resCheck k M fuel r`: residue `r` mod `2^k` is fine for all `n = 2^k m + r`, `m < M`.
* `cycleCheck N b`: no cycle with `b` odd steps has all odd elements `≥ N`.
-/

namespace Collatz

/-- One accelerated step is one or two Collatz steps. -/
lemma kstepT_iter (x : ℕ) : ∃ j, 1 ≤ j ∧ step^[j] x = kstepT x := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · exact ⟨1, le_rfl, by simp [kstepT, step_even h, h]⟩
  · refine ⟨2, by norm_num, ?_⟩
    have h2 : (3 * x + 1) % 2 = 0 := by omega
    simp [kstepT, h, step_odd h, step_even h2]

lemma kdesc_spec {n0 : ℕ} :
    ∀ {fuel x : ℕ}, kdesc n0 fuel x = true → ∃ j, 1 ≤ j ∧ step^[j] x < n0
  | 0, x, h => by
    have : kdesc n0 0 x = false := rfl
    simp [this] at h
  | f + 1, x, h => by
    have e : kdesc n0 (f + 1) x = ((kstepT x).blt n0 || kdesc n0 f (kstepT x)) := rfl
    rw [e, Bool.or_eq_true, Nat.blt_eq] at h
    obtain ⟨j0, hj0, he0⟩ := kstepT_iter x
    rcases h with h | h
    · exact ⟨j0, hj0, he0 ▸ h⟩
    · obtain ⟨j, hj, he⟩ := kdesc_spec h
      exact ⟨j + j0, by omega, by rw [Function.iterate_add_apply, he0]; exact he⟩

lemma kall_spec {f : ℕ → Bool} : ∀ {n : ℕ}, kall f n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : kall f (n + 1) = (f n && kall f n) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact kall_spec h.2 i hi
    · exact h.1

theorem descends_of_resCheck {k M fuel : ℕ} (h : ∀ r < 2 ^ k, resCheck k M fuel r = true) :
    ∀ n, 2 ≤ n → n < 2 ^ k * M → Descends n := by
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
      · rw [hnr]; exact kdesc_spec hs
    · exact descends_of_cert hc rfl
        (by have := Nat.mul_le_mul_left (2 ^ k) hpos; omega)
  · have := kall_spec hall m hmM
    rw [Bool.or_eq_true, Nat.blt_eq, hnm] at this
    rcases this with hs | hs
    · omega
    · exact kdesc_spec hs

lemma kallFrom_spec {f : ℕ → Bool} {lo len : ℕ} (h : kallFrom f lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → f i = true := by
  intro i h1 h2
  have := kall_spec h (i - lo) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

lemma kallFrom_append {f : ℕ → Bool} {lo l1 l2 : ℕ} (h1 : kallFrom f lo l1 = true)
    (h2 : kallFrom f (lo + l1) l2 = true) : kallFrom f lo (l1 + l2) = true := by
  have s1 := kallFrom_spec h1
  have s2 := kallFrom_spec h2
  unfold kallFrom
  suffices ∀ n, n ≤ l1 + l2 → kall (fun i => f (lo + i)) n = true from this _ le_rfl
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
    intro hn
    have e : kall (fun i => f (lo + i)) (n + 1) = (f (lo + n) && kall (fun i => f (lo + i)) n) :=
      rfl
    rw [e, Bool.and_eq_true]
    refine ⟨?_, ih (by omega)⟩
    rcases Nat.lt_or_ge n l1 with h | h
    · exact s1 _ (by omega) (by omega)
    · exact s2 _ (by omega) (by omega)

lemma kall_of_kallFrom {f : ℕ → Bool} {n : ℕ} (h : kallFrom f 0 n = true) :
    ∀ i < n, f i = true := fun i hi => kallFrom_spec h i (Nat.zero_le _) (by omega)

lemma kall_of_kallFrom_zero {f : ℕ → Bool} {n : ℕ} (h : kallFrom f 0 n = true) :
    kall f n = true := by
  simpa [kallFrom] using h

/-! ## Cycles -/

/-- No cycle with `b` odd steps whose odd elements are all `≥ N`: the smallest admissible
`a = log2 (3^b) + 1` already violates the upper bound. -/
def cycleCheck (N b : ℕ) : Bool :=
  b == 0 || !(Nat.ble (N ^ b * 2 ^ (Nat.log2 (3 ^ b) + 1)) ((3 * N + 1) ^ b))

lemma log2_lt_of_lt_two_pow {x a : ℕ} (hx : 1 ≤ x) (h : x < 2 ^ a) : Nat.log2 x < a :=
  (Nat.log2_lt (by omega)).2 h

theorem odds_card_ge_of_check {n p N B : ℕ} (hc : IsCycle n p) (hnr : ¬ ReachesOne n)
    (hsmall : ∀ y, 1 ≤ y → y < N → ReachesOne y)
    (hchk : kall (cycleCheck N) B = true) : B ≤ (odds n p).card := by
  have hm : ∀ i ∈ odds n p, N ≤ step^[i] n := by
    intro i _
    by_contra hlt
    exact not_reachesOne_iterate hnr i (hsmall _ (iterate_pos hc.1 i) (by omega))
  have hup := two_pow_le hc hm
  have hlow := three_pow_lt_two_pow hc
  by_contra hb
  have h1 := kall_spec hchk _ (by omega : (odds n p).card < B)
  unfold cycleCheck at h1
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  rcases h1 with h0 | h1
  · exact absurd h0 (Nat.pos_iff_ne_zero.1 (Finset.card_pos.2 (odds_nonempty hc)))
  · have hnle : ¬ (N ^ (odds n p).card * 2 ^ (Nat.log2 (3 ^ (odds n p).card) + 1)
        ≤ (3 * N + 1) ^ (odds n p).card) := by
      rw [← Nat.ble_eq]; simp [h1]
    have ha : Nat.log2 (3 ^ (odds n p).card) + 1 ≤ (evens n p).card :=
      log2_lt_of_lt_two_pow (Nat.one_le_pow _ _ (by norm_num)) hlow
    have : N ^ (odds n p).card * 2 ^ (Nat.log2 (3 ^ (odds n p).card) + 1)
        ≤ N ^ (odds n p).card * 2 ^ (evens n p).card :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) ha)
    omega

theorem evens_card_ge_of_odds {n p B : ℕ} (hc : IsCycle n p) (hB : B ≤ (odds n p).card) :
    Nat.log2 (3 ^ B) + 1 ≤ (evens n p).card := by
  have h1 : 3 ^ B ≤ 3 ^ (odds n p).card := Nat.pow_le_pow_right (by norm_num) hB
  exact log2_lt_of_lt_two_pow (Nat.one_le_pow _ _ (by norm_num))
    (lt_of_le_of_lt h1 (three_pow_lt_two_pow hc))

end Collatz
