import Collatz.Descent

/-!
# Residue-class descent certificates (Terras-style)

Write `n = 2^k * m + r` with `r < 2^k`. As long as the coefficient of `m` is even, the parity
of the current value `a * m + b` is the parity of `b`, so the first few Collatz steps are
determined by `r` alone and the orbit can be tracked symbolically as an affine function of `m`.

If at some point the affine form `a' * m + b'` satisfies `a' < 2^k` and `b' ≤ r`, then every
`n ≥ 2^k` in the residue class `r` descends. `cert k r` runs this symbolic computation, and
`descends_of_cert` proves it sound. Residues that cannot be certified are the `survivors`.
-/

namespace Collatz

/-- One symbolic step on the affine form `a * m + b` (valid when `a` is even). -/
def next (a b : ℕ) : ℕ × ℕ := if b % 2 = 0 then (a / 2, b / 2) else (3 * a, 3 * b + 1)

lemma step_affine {a b : ℕ} (ha : a % 2 = 0) (m : ℕ) :
    step (a * m + b) = (next a b).1 * m + (next a b).2 := by
  obtain ⟨a0, rfl⟩ : ∃ a0, a = 2 * a0 := ⟨a / 2, by omega⟩
  unfold next
  split_ifs with hb
  · obtain ⟨b0, rfl⟩ : ∃ b0, b = 2 * b0 := ⟨b / 2, by omega⟩
    have e : 2 * a0 * m + 2 * b0 = 2 * (a0 * m + b0) := by ring
    rw [e, step_even (by omega)]
    simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · have e : 2 * a0 * m + b = 2 * (a0 * m) + b := by ring
    rw [step_odd (by omega)]
    ring

/-- Symbolic run with fuel, checking for a certificate of descent. -/
def certAux (K r : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if a % 2 = 0 then
      if (next a b).1 < K ∧ (next a b).2 ≤ r then true
      else certAux K r fuel (next a b).1 (next a b).2
    else false

lemma certAux_spec {K r : ℕ} :
    ∀ {fuel a b : ℕ}, certAux K r fuel a b = true → ∀ m : ℕ,
      ∃ j a' b', 1 ≤ j ∧ a' < K ∧ b' ≤ r ∧ step^[j] (a * m + b) = a' * m + b'
  | 0, _, _, h, _ => by simp [certAux] at h
  | fuel + 1, a, b, h, m => by
    unfold certAux at h
    split_ifs at h with ha hc
    · exact ⟨1, _, _, le_rfl, hc.1, hc.2, by simpa using step_affine ha m⟩
    · obtain ⟨j, a', b', hj, ha', hb', he⟩ := certAux_spec h m
      refine ⟨j + 1, a', b', by omega, ha', hb', ?_⟩
      rw [Function.iterate_succ_apply, step_affine ha m, he]

/-- `cert k r = true` certifies that every `n ≥ 2^k` with `n % 2^k = r` descends. -/
def cert (k r : ℕ) : Bool := certAux (2 ^ k) r (2 * k + 1) (2 ^ k) r

theorem descends_of_cert {k r n : ℕ} (h : cert k r = true) (hr : n % 2 ^ k = r)
    (hn : 2 ^ k ≤ n) : Descends n := by
  have hK : 0 < 2 ^ k := by positivity
  have hm : 1 ≤ n / 2 ^ k := (Nat.one_le_div_iff hK).2 hn
  obtain ⟨j, a', b', hj, ha', hb', he⟩ := certAux_spec h (n / 2 ^ k)
  have hn' : 2 ^ k * (n / 2 ^ k) + r = n := by rw [← hr]; exact Nat.div_add_mod n (2 ^ k)
  rw [hn'] at he
  refine ⟨j, hj, ?_⟩
  rw [he]
  have : a' * (n / 2 ^ k) < 2 ^ k * (n / 2 ^ k) := Nat.mul_lt_mul_of_pos_right ha' hm
  omega

/-- Residues mod `2^k` that `cert` cannot certify. -/
def survivors (k : ℕ) : List ℕ := (List.range (2 ^ k)).filter (fun r => !cert k r)

/-- Only the surviving residue classes need to be handled (for `n ≥ 2^k`). -/
theorem descends_large_of_survivors (k : ℕ)
    (h : ∀ n, 2 ^ k ≤ n → n % 2 ^ k ∈ survivors k → Descends n) :
    ∀ n, 2 ^ k ≤ n → Descends n := by
  intro n hn
  by_cases hc : cert k (n % 2 ^ k) = true
  · exact descends_of_cert hc rfl hn
  · apply h n hn
    simp only [survivors, List.mem_filter, List.mem_range]
    exact ⟨Nat.mod_lt _ (by positivity), by simpa using hc⟩

end Collatz
