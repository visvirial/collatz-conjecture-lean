import Collatz.LSF.Basic
import Collatz.LongStopGen

/-!
# Soundness of the run-based certificate check

`Collatz.LSF.runsOk` (see `Collatz/LSF/Basic.lean`) checks the condition of `Collatz.LSCert`
per source residue `s < M` prime to `3`, on consecutive runs of residues. This file proves that
successful checks covering `[0, M)` give `LSCert` (`lsCert_of_good`), so that
`Collatz.long_stopping_log_gen` applies; the bound `H = 2^W - 1` on the potential is automatic
(`pot_lt`).

The certificate is the same one-step potential certificate as in `Collatz.LongStopGen`; only the
check is reorganised (per source instead of per lift, runs with literal piece indices, bare `Nat`
functions), which makes it about 15 times cheaper per residue than `Collatz.LS12` and allows the
moduli `3^14` and `3^15` (`Collatz.LongStop14`, `Collatz.LongStop15`).
-/

namespace Collatz.LSF

/-- The certificate condition at the source residue `s`, for its three lifts `s + kM`. -/
def Good (h : ℕ → ℕ) (M P Q s : ℕ) : Prop :=
  s % 3 = 0 ∨ h s + P ≤ h (2 * s % M) ∨
    ((s % 9 = 2 ∨ s % 9 = 8) ∧ h s + P ≤ h ((2 * s - 1) / 3 % M) + Q ∧
      h s + P ≤ h ((2 * (s + M) - 1) / 3 % M) + Q ∧
      h s + P ≤ h ((2 * (s + 2 * M) - 1) / 3 % M) + Q)

/-! The kernel definitions of `Collatz/LSF/Basic.lean` with the usual notation. -/

lemma ent_def (S W B r : ℕ) : ent S W B r = (B >>> (W * (r % S))) % 2 ^ W := rfl

lemma pot_def (pc : ℕ → ℕ) (S W r : ℕ) : pot pc S W r = ent S W (pc (r / S)) r := rfl

lemma oddOk_def (S W Q hs B c o : ℕ) :
    oddOk S W Q hs B c o = (Nat.beq (o / S) c && Nat.ble hs (ent S W B o + Q)) := rfl

lemma okAt_def (S W M P Q Bs a Be b B0 c0 B1 c1 B2 c2 s : ℕ) :
    okAt S W M P Q Bs a Be b B0 c0 B1 c1 B2 c2 s =
        (Nat.beq (s / S) a &&
          ((Nat.beq (2 * s % M / S) b && Nat.ble (ent S W Bs s + P) (ent S W Be (2 * s % M))) ||
            ((Nat.beq (s % 9) 2 || Nat.beq (s % 9) 8) &&
              oddOk S W Q (ent S W Bs s + P) B0 c0 ((2 * s - 1) / 3 % M) &&
              oddOk S W Q (ent S W Bs s + P) B1 c1 ((2 * (s + M) - 1) / 3 % M) &&
              oddOk S W Q (ent S W Bs s + P) B2 c2 ((2 * (s + 2 * M) - 1) / 3 % M)))) := rfl

lemma kfrom_spec {f g : ℕ → Bool} {lo : ℕ} :
    ∀ {len : ℕ}, kfrom f g lo len = true →
      ∀ s, 3 * lo ≤ s → s < 3 * (lo + len) →
        (s % 3 = 1 → f s = true) ∧ (s % 3 = 2 → g s = true)
  | 0, _, s, h1, h2 => by omega
  | len + 1, h, s, h1, h2 => by
    have e : kfrom f g lo (len + 1) =
        (f (3 * (lo + len) + 1) && g (3 * (lo + len) + 2) && kfrom f g lo len) := rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge s (3 * (lo + len)) with hs | hs
    · exact kfrom_spec h.2 s h1 hs
    · constructor
      · intro h3; rw [show s = 3 * (lo + len) + 1 by omega]; exact h.1.1
      · intro h3; rw [show s = 3 * (lo + len) + 2 by omega]; exact h.1.2

lemma runsLen_cons (len a b1 b2 c0 c1 c2 : ℕ) (rs : List Run) :
    runsLen ((len, a, b1, b2, c0, c1, c2) :: rs) = len + runsLen rs := rfl

lemma runsOk_cons (pc : ℕ → ℕ) (S W M P Q len a b1 b2 c0 c1 c2 lo : ℕ) (rs : List Run) :
    runsOk pc S W M P Q ((len, a, b1, b2, c0, c1, c2) :: rs) lo =
      (kfrom (okAt S W M P Q (pc a) a (pc b1) b1 (pc c0) c0 (pc c1) c1 (pc c2) c2)
        (okAt S W M P Q (pc a) a (pc b2) b2 (pc c0) c0 (pc c1) c1 (pc c2) c2) lo len &&
        runsOk pc S W M P Q rs (lo + len)) := rfl

/-! ## Soundness -/

lemma ent_eq {pc : ℕ → ℕ} {S W a r : ℕ} (h : r / S = a) : ent S W (pc a) r = pot pc S W r := by
  rw [pot_def, h]

lemma oddOk_spec {pc : ℕ → ℕ} {S W Q hs c o : ℕ} (h : oddOk S W Q hs (pc c) c o = true) :
    hs ≤ pot pc S W o + Q := by
  rw [oddOk_def] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  rw [← ent_eq h.1]; exact h.2

lemma okAt_spec {pc : ℕ → ℕ} {S W M P Q a b c0 c1 c2 s : ℕ}
    (h : okAt S W M P Q (pc a) a (pc b) b (pc c0) c0 (pc c1) c1 (pc c2) c2 s = true) :
    Good (pot pc S W) M P Q s := by
  rw [okAt_def] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  rcases h with ⟨ha, ⟨hb, he⟩ | ⟨⟨⟨h9, o0⟩, o1⟩, o2⟩⟩
  · right; left
    rw [← ent_eq ha, ← ent_eq hb]; exact he
  · right; right
    have o0 := oddOk_spec o0
    have o1 := oddOk_spec o1
    have o2 := oddOk_spec o2
    rw [ent_eq ha] at o0 o1 o2
    exact ⟨h9, o0, o1, o2⟩

lemma runsOk_spec {pc : ℕ → ℕ} {S W M P Q : ℕ} :
    ∀ {rs : List Run} {lo : ℕ}, runsOk pc S W M P Q rs lo = true →
      ∀ s, 3 * lo ≤ s → s < 3 * (lo + runsLen rs) → Good (pot pc S W) M P Q s
  | [], lo, _, s, h1, h2 => by
    have : runsLen [] = 0 := rfl
    omega
  | (len, a, b1, b2, c0, c1, c2) :: rs, lo, h, s, h1, h2 => by
    rw [runsOk_cons, Bool.and_eq_true] at h
    rw [runsLen_cons] at h2
    rcases Nat.lt_or_ge s (3 * (lo + len)) with hs | hs
    · have hk := kfrom_spec h.1 s h1 hs
      rcases (by omega : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2) with h3 | h3 | h3
      · exact Or.inl h3
      · exact okAt_spec (hk.1 h3)
      · exact okAt_spec (hk.2 h3)
    · exact runsOk_spec h.2 s hs (by omega)

/-- Per-source conditions for all `s < M` give the certificate `LSCert`. -/
theorem lsCert_of_good {h : ℕ → ℕ} {M P Q : ℕ} (h9 : 9 ∣ M)
    (hg : ∀ s < M, Good h M P Q s) : LSCert h M P Q := by
  intro t ht h3
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; omega)
  set s := t % M with hs
  have hsM : s < M := Nat.mod_lt _ hM
  have hdiv : M * (t / M) + s = t := Nat.div_add_mod t M
  have hk : t / M < 3 := by
    rw [Nat.div_lt_iff_lt_mul hM]; linarith
  have e9 : s % 9 = t % 9 := Nat.mod_mod_of_dvd t h9
  have e3 : s % 3 = t % 3 :=
    Nat.mod_mod_of_dvd t (dvd_trans (by norm_num : (3 : ℕ) ∣ 9) h9)
  have e2 : 2 * t % M = 2 * s % M := by rw [hs, Nat.mul_mod_mod]
  rcases hg s hsM with h0 | he | ⟨h9', o0, o1, o2⟩
  · omega
  · left; rw [e2]; exact he
  · right
    refine ⟨by omega, ?_⟩
    have ho : (2 * t - 1) / 3 % M = (2 * s - 1) / 3 % M ∨
        (2 * t - 1) / 3 % M = (2 * (s + M) - 1) / 3 % M ∨
        (2 * t - 1) / 3 % M = (2 * (s + 2 * M) - 1) / 3 % M := by
      interval_cases hq : t / M
      · left; congr 3; omega
      · right; left; congr 3; omega
      · right; right; congr 3; omega
    rcases ho with e | e | e <;> rw [e] <;> assumption

/-- The potential is below `2^W`. -/
lemma pot_lt (pc : ℕ → ℕ) (S W r : ℕ) : pot pc S W r < 2 ^ W := by
  rw [pot_def, ent_def]; exact Nat.mod_lt _ (Nat.two_pow_pos W)

end Collatz.LSF
