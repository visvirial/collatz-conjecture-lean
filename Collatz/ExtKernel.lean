import Collatz.ExtDefs
import Collatz.CoeffStop

/-!
# Soundness of the extension checker `resExt`

`sieveExt_spec` is the generic soundness statement for any property `P` that follows from a
certificate at a level `j ≤ k` and from a direct `kdesc` check. It gives

* `descends_of_resExt`: the existing `resCheck k M0 fuel` facts together with
  `resExt j0 d M0 M1 fuel` (`j0 + d = k`) give `Descends n` for all `2 ≤ n < 2^k * M1`;
* `kstepT_descends_of_resExt`: the bounded version in accelerated steps (as
  `kstepT_descends_of_resCheck`, used by `Collatz.cst_of_tables`).
-/

namespace Collatz

/-- Generic soundness of `sieveExt`. -/
theorem sieveExt_spec (P : ℕ → Prop) {k M0 M1 fuel : ℕ} (hM0 : 1 ≤ M0)
    (hcert : ∀ j n, j ≤ k → cert j (n % 2 ^ j) = true → 2 ^ j ≤ n → P n)
    (hkd : ∀ n, kdesc n fuel n = true → P n) :
    ∀ d j r, j + d ≤ k → sieveExt M0 M1 fuel d j r = true → ∀ n, n % 2 ^ j = r →
      2 ^ (j + d) * M0 ≤ n → n < 2 ^ (j + d) * M1 → P n := by
  intro d
  induction d with
  | zero =>
    intro j r hjk h n hr h0 h1
    have e : sieveExt M0 M1 fuel 0 j r = (cert j r ||
        kallFrom (fun m => kdesc (2 ^ j * m + r) fuel (2 ^ j * m + r)) M0 (M1 - M0)) := rfl
    rw [e, Bool.or_eq_true] at h
    rw [Nat.add_zero] at h0 h1
    have hpos : 0 < 2 ^ j := by positivity
    rcases h with hc | hall
    · exact hcert j n (by omega) (hr ▸ hc) (le_trans (Nat.le_mul_of_pos_right _ hM0) h0)
    · have hnm : 2 ^ j * (n / 2 ^ j) + r = n := by rw [← hr]; exact Nat.div_add_mod n (2 ^ j)
      have hm0 : M0 ≤ n / 2 ^ j := (Nat.le_div_iff_mul_le hpos).2 (by rw [mul_comm]; exact h0)
      have hm1 : n / 2 ^ j < M1 := (Nat.div_lt_iff_lt_mul hpos).2 (by rw [mul_comm]; exact h1)
      have := kallFrom_spec hall (n / 2 ^ j) hm0 (by omega)
      rw [hnm] at this
      exact hkd n this
  | succ d ih =>
    intro j r hjk h n hr h0 h1
    have e : sieveExt M0 M1 fuel (d + 1) j r = (cert j r ||
        (sieveExt M0 M1 fuel d (j + 1) r && sieveExt M0 M1 fuel d (j + 1) (r + 2 ^ j))) := rfl
    rw [e, Bool.or_eq_true, Bool.and_eq_true] at h
    rw [show j + (d + 1) = (j + 1) + d by omega] at h0 h1
    rcases h with hc | ⟨ha, hb⟩
    · have h2 : 2 ^ j ≤ 2 ^ (j + 1 + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hcert j n (by omega) (hr ▸ hc)
        (le_trans h2 (le_trans (Nat.le_mul_of_pos_right _ hM0) h0))
    · have hsplit := (Nat.mod_pow_succ (x := n) (b := 2) (k := j))
      rw [hr] at hsplit
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with hp | hp
      · rw [hp, Nat.mul_zero, Nat.add_zero] at hsplit
        exact ih (j + 1) r (by omega) ha n hsplit h0 h1
      · rw [hp, Nat.mul_one] at hsplit
        exact ih (j + 1) (r + 2 ^ j) (by omega) hb n hsplit h0 h1

/-- Combining the existing `resCheck` range with the `resExt` range. -/
theorem of_resCheck_resExt (P : ℕ → Prop) {k j0 d M0 M1 fuel : ℕ} (hk : j0 + d = k)
    (hM0 : 1 ≤ M0)
    (hlow : ∀ n, 2 ≤ n → n < 2 ^ k * M0 → P n)
    (hcert : ∀ j n, j ≤ k → cert j (n % 2 ^ j) = true → 2 ^ j ≤ n → P n)
    (hkd : ∀ n, kdesc n fuel n = true → P n)
    (h1 : ∀ r < 2 ^ j0, resExt j0 d M0 M1 fuel r = true) :
    ∀ n, 2 ≤ n → n < 2 ^ k * M1 → P n := by
  intro n hn2 hn
  rcases Nat.lt_or_ge n (2 ^ k * M0) with hlt | hge
  · exact hlow n hn2 hlt
  · subst hk
    exact sieveExt_spec P hM0 hcert hkd d j0 (n % 2 ^ j0) le_rfl
      (h1 _ (Nat.mod_lt _ (by positivity))) n rfl hge hn

/-- **Soundness of the extension**: the old residue check up to `2^k * M0` and the sieve
`resExt` for `2^k * M0 ≤ n < 2^k * M1` give descent of every `2 ≤ n < 2^k * M1`. -/
theorem descends_of_resExt {k j0 d M0 M1 fuel : ℕ} (hk : j0 + d = k) (hM0 : 1 ≤ M0)
    (h0 : ∀ r < 2 ^ k, resCheck k M0 fuel r = true)
    (h1 : ∀ r < 2 ^ j0, resExt j0 d M0 M1 fuel r = true) :
    ∀ n, 2 ≤ n → n < 2 ^ k * M1 → Descends n :=
  of_resCheck_resExt Descends hk hM0 (descends_of_resCheck h0)
    (fun _ _ _ hc hn => descends_of_cert hc rfl hn) (fun _ h => kdesc_spec h) h1

/-- Bounded version of `descends_of_resExt`, in accelerated steps. -/
theorem kstepT_descends_of_resExt {k j0 d M0 M1 fuel : ℕ} (hk : j0 + d = k) (hM0 : 1 ≤ M0)
    (h0 : ∀ r < 2 ^ k, resCheck k M0 fuel r = true)
    (h1 : ∀ r < 2 ^ j0, resExt j0 d M0 M1 fuel r = true) :
    ∀ n, 2 ≤ n → n < 2 ^ k * M1 → ∃ i, 1 ≤ i ∧ i ≤ max fuel (2 * k + 1) ∧ kstepT^[i] n < n := by
  refine of_resCheck_resExt _ hk hM0 (kstepT_descends_of_resCheck h0) ?_ ?_ h1
  · intro j n hj hc hn
    have hK : 0 < 2 ^ j := by positivity
    have hpos : 1 ≤ n / 2 ^ j := (Nat.one_le_div_iff hK).2 hn
    obtain ⟨i, a', b', hi, hif, ha', hb', he⟩ := certAux_spec_bounded hc (n / 2 ^ j)
    rw [Nat.div_add_mod n (2 ^ j)] at he
    have hlt : step^[i] n < n := by
      rw [he]
      have : a' * (n / 2 ^ j) < 2 ^ j * (n / 2 ^ j) := Nat.mul_lt_mul_of_pos_right ha' hpos
      have := Nat.div_add_mod n (2 ^ j)
      omega
    obtain ⟨i', hi', hii, hT⟩ := kstepT_lt_of_step_lt hlt
    exact ⟨i', hi', le_trans hii (le_trans hif (le_trans (by omega) (le_max_right _ _))), hT⟩
  · intro n h
    obtain ⟨i, hi, hif, he⟩ := kdesc_spec_T h
    exact ⟨i, hi, le_trans hif (le_max_left _ _), he⟩

end Collatz
