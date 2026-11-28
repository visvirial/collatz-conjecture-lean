import Collatz.Terras

/-!
# The sufficiency of arithmetic progressions for the 3x+1 conjecture

Reference: K. M. Monks, *The sufficiency of arithmetic progressions for the 3x+1 conjecture*,
Proc. Amer. Math. Soc. **134** (2006), no. 10, 2861–2872 (MR2231609). The proof below follows
the sketch in Keenan Monks, K. G. Monks, K. M. Monks, M. Monks, *Strongly sufficient sets and the
distribution of arithmetic sequences in the 3x+1 graph*, arXiv:1204.3904, Sec. 3 (eq. (3.1))
and Sec. 4 (Lemma 4.3, Theorem 4.1).

Main results (namespace `Collatz.MonksAP`):
* `exists_pred_mod`: if `3 ∤ m`, every residue class `a mod d` (`d ≥ 1`) contains arbitrarily
  large `y` with `T^K y = m` for some `K` (`T = kstepT`).
* `conjecture_of_arith_prog`, `conjecture_iff_arith_prog` (Monks' theorem): the conjecture
  holds iff it holds for the positive members of one progression `{a + d n : n ≥ 0}`, `d ≥ 1`.
* Analogues for the other two conjectures, from the same key lemma:
  `exists_unbounded_of_unbounded` (an unbounded positive orbit forces an unbounded orbit in
  the progression), `exists_not_reachesOne` (an orbit not reaching `1` merges with that of a
  progression member not reaching `1`) and `exists_reaches_cycle` (every cycle, in particular
  every nontrivial one, is entered by the orbit of a progression member). These are the
  orbit-merging forms of the divergence and cycle statements; Monks' paper phrases them for the
  corresponding conjectures, and the statements here imply those reductions.

Proof outline. The backward maps `P0 z = 2z` and `P1 z = (2z - 1)/3` (for `z ≡ 2 mod 3`) undo
`T`; a word is a list of them (`Adm`, `app`, `kstepT_app`).
* (A) For `b` coprime to `6` and `f + 1 = φ(b)`, the block `s₁ = P0^f P1 P0^f P1^f P0^2` acts on
  `ZMod b` as `x ↦ x + 1` (`blk_mod`), a form of Monks et al. (3.1).
* (B) For any word `w` with `ℓ` odd steps and any `ρ` mod `3^M` there is a class mod
  `3^(M+ℓ)` on which `w` is admissible with output `≡ ρ (mod 3^M)` (`adm_class`).
* (C) `2` is a primitive root mod `3^N` (`two_pow_hit`, from
  `ZMod.orderOf_one_add_mul_prime`), so `2^k m` reaches every unit class (`hit_unit`).
* (D) A prefix of `s₁^(b+1)` applied to a suitable `2^k m` gives an ancestor `y₀` of `m` with
  `b ∣ y₀`, `3 ∤ y₀` (`exists_zero_mod`).
* (E) Then `s₁^j (2^k y₀)` with `j ≡ β (mod b)` and `k` chosen 3-adically gives ancestors in any
  class mod `b` and mod `3^L` (`exists_odd_mod`).
* (F) The 2-adic part of `d` is handled by Terras' affine formula `iterate_affine`.
-/

namespace Collatz.MonksAP

open Collatz

/-! ## (C) `2` is a primitive root modulo `3^N` -/

lemma coprime_three_pow {x : ℕ} (hx : x % 3 ≠ 0) (N : ℕ) : Nat.Coprime x (3 ^ N) := by
  apply Nat.Coprime.pow_right
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).symm

lemma two_pow_hit (N κ : ℕ) (hκ : κ % 3 ≠ 0) : ∃ k, 2 ^ k ≡ κ [MOD 3 ^ N] := by
  rcases N with _ | n
  · exact ⟨0, by simp [Nat.ModEq, Nat.mod_one]⟩
  have : NeZero (3 ^ (n + 1)) := ⟨by positivity⟩
  have hc2 : Nat.Coprime 2 (3 ^ (n + 1)) := coprime_three_pow (by norm_num) _
  set u : (ZMod (3 ^ (n + 1)))ˣ := ZMod.unitOfCoprime 2 hc2 with hu
  have hu2 : ((u ^ 2 : (ZMod (3 ^ (n + 1)))ˣ) : ZMod (3 ^ (n + 1))) =
      1 + ((3 : ℕ) : ZMod (3 ^ (n + 1))) * ((1 : ℤ) : ZMod (3 ^ (n + 1))) := by
    simp [hu]; norm_num
  have h4 : orderOf (u ^ 2) = 3 ^ n := by
    rw [← orderOf_units, hu2]
    exact ZMod.orderOf_one_add_mul_prime Nat.prime_three (by norm_num) 1 (by norm_num) n
  have hcard : Nat.card (ZMod (3 ^ (n + 1)))ˣ = 2 * 3 ^ n := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ Nat.prime_three]
    ring
  have hdvd : orderOf u ∣ 2 * 3 ^ n := hcard ▸ orderOf_dvd_natCard u
  rw [orderOf_pow' u (by norm_num)] at h4
  have hord : orderOf u = 2 * 3 ^ n := by
    have hpos : 0 < orderOf u := orderOf_pos u
    rcases Nat.coprime_or_dvd_of_prime Nat.prime_two (orderOf u) with hcop | h2
    · exfalso
      have hg : Nat.gcd (orderOf u) 2 = 1 := Nat.Coprime.symm hcop
      rw [hg, Nat.div_one] at h4
      have h1 : u ^ (3 ^ n) = 1 := h4 ▸ pow_orderOf_eq_one u
      have h1' : ((2 : ℕ) : ZMod (3 ^ (n + 1))) ^ (3 ^ n) = ((1 : ℕ) : ZMod (3 ^ (n + 1))) := by
        have := congrArg (fun v : (ZMod (3 ^ (n + 1)))ˣ => (v : ZMod (3 ^ (n + 1)))) h1
        simpa [hu] using this
      rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h1'
      have h3 : 2 ^ (3 ^ n) ≡ 1 [MOD 3] := Nat.ModEq.of_dvd (dvd_pow_self 3 (by omega)) h1'
      have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := hodd
      rw [ht, pow_succ, pow_mul] at h3
      have : (4 ^ t * 2) % 3 = 2 := by
        rw [Nat.mul_mod, Nat.pow_mod]; norm_num
      unfold Nat.ModEq at h3
      norm_num at h3
      omega
    · have hg : Nat.gcd (orderOf u) 2 = 2 := Nat.gcd_eq_right h2
      rw [hg] at h4
      obtain ⟨q, hq⟩ := h2
      rw [hq, Nat.mul_div_cancel_left _ (by norm_num)] at h4
      rw [hq, h4]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  set v : (ZMod (3 ^ (n + 1)))ˣ := ZMod.unitOfCoprime κ (coprime_three_pow hκ _) with hv
  have hmem : v ∈ Submonoid.powers u := by
    rw [mem_powers_iff_mem_zpowers, htop]; exact Subgroup.mem_top v
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have := congrArg (fun w : (ZMod (3 ^ (n + 1)))ˣ => (w : ZMod (3 ^ (n + 1)))) hk
  simpa [hu, hv] using this

/-- Multiplying a unit by powers of `2` reaches every unit class modulo `3^N`. -/
lemma hit_unit (N κ z : ℕ) (hκ : κ % 3 ≠ 0) (hz : z % 3 ≠ 0) :
    ∃ k, 2 ^ k * z ≡ κ [MOD 3 ^ N] := by
  set T := Nat.totient (3 ^ N)
  have hT : 0 < T := Nat.totient_pos.2 (by positivity)
  have hzT : z ^ T ≡ 1 [MOD 3 ^ N] := Nat.ModEq.pow_totient (coprime_three_pow hz N)
  have hu : (κ * z ^ (T - 1)) % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ κ * z ^ (T - 1) := by omega
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega
  obtain ⟨k, hk⟩ := two_pow_hit N _ hu
  refine ⟨k, ?_⟩
  calc 2 ^ k * z ≡ κ * z ^ (T - 1) * z [MOD 3 ^ N] := hk.mul_right z
    _ = κ * z ^ T := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hT]
    _ ≡ κ * 1 [MOD 3 ^ N] := hzT.mul_left κ
    _ = κ := mul_one κ

lemma two_pow_period (N k t : ℕ) :
    2 ^ (k + t * Nat.totient (3 ^ N)) ≡ 2 ^ k [MOD 3 ^ N] := by
  have h := Nat.ModEq.pow_totient (coprime_three_pow (x := 2) (by norm_num) N)
  rw [pow_add, mul_comm t, pow_mul]
  calc 2 ^ k * (2 ^ Nat.totient (3 ^ N)) ^ t ≡ 2 ^ k * 1 ^ t [MOD 3 ^ N] :=
        (h.pow t).mul_left _
    _ = 2 ^ k := by simp

/-! ## Backward words -/

/-- The two backward maps of the accelerated map `T = kstepT`: `P false z = 2z` and
`P true z = (2z - 1)/3` (the latter is a genuine `T`-preimage when `z ≡ 2 (mod 3)`). -/
def P : Bool → ℕ → ℕ
  | false, z => 2 * z
  | true, z => (2 * z - 1) / 3

/-- A word (list of backward maps, in application order) is admissible at `z`. -/
def Adm : List Bool → ℕ → Prop
  | [], _ => True
  | b :: w, z => (b = true → z % 3 = 2) ∧ Adm w (P b z)

/-- The result of applying a word to `z`. -/
def app : List Bool → ℕ → ℕ
  | [], z => z
  | b :: w, z => app w (P b z)

lemma kstepT_P (b : Bool) (z : ℕ) (h : b = true → z % 3 = 2) : kstepT (P b z) = z := by
  cases b
  · simp only [P]; rw [kstepT_of_even (by omega)]; omega
  · have h2 := h rfl
    simp only [P]
    rw [kstepT_of_odd (by omega)]; omega

lemma kstepT_app : ∀ (w : List Bool) (z : ℕ), Adm w z → kstepT^[w.length] (app w z) = z
  | [], _, _ => rfl
  | b :: w, z, h => by
    simp only [Adm] at h
    simp only [app, List.length_cons]
    rw [Function.iterate_succ_apply', kstepT_app w _ h.2, kstepT_P b z h.1]

lemma adm_append : ∀ (w1 w2 : List Bool) (z : ℕ),
    Adm (w1 ++ w2) z ↔ Adm w1 z ∧ Adm w2 (app w1 z)
  | [], _, _ => by simp [Adm, app]
  | b :: w, w2, z => by
    simp only [List.cons_append, Adm, app]
    rw [adm_append w w2]; tauto

lemma app_append : ∀ (w1 w2 : List Bool) (z : ℕ), app (w1 ++ w2) z = app w2 (app w1 z)
  | [], _, _ => rfl
  | b :: w, w2, z => by simp only [List.cons_append, app]; exact app_append w w2 _

lemma adm_unit : ∀ (w : List Bool) (z : ℕ), Adm w z → true ∈ w → z % 3 ≠ 0
  | [], _, _, h => by simp at h
  | b :: w, z, h, hm => by
    cases b
    · simp only [Adm, P] at h
      have hm' : true ∈ w := by simpa using hm
      have := adm_unit w _ h.2 hm'
      omega
    · simp only [Adm] at h
      have := h.1 trivial; omega

lemma app_rep_false : ∀ (n z : ℕ), app (List.replicate n false) z = 2 ^ n * z
  | 0, z => by simp [app]
  | n + 1, z => by
    rw [List.replicate_succ]; simp only [app, P]
    rw [app_rep_false n]; ring

lemma adm_rep_false : ∀ (n z : ℕ), Adm (List.replicate n false) z
  | 0, _ => trivial
  | n + 1, z => by
    rw [List.replicate_succ]; exact ⟨by simp, adm_rep_false n _⟩

lemma app_rep_true : ∀ (n z : ℕ), Adm (List.replicate n true) z →
    3 ^ n * (app (List.replicate n true) z + 1) = 2 ^ n * (z + 1)
  | 0, z, _ => by simp [app]
  | n + 1, z, h => by
    rw [List.replicate_succ] at h ⊢
    simp only [Adm, P] at h
    simp only [app, P]
    have ih := app_rep_true n _ h.2
    have h3 : 3 * ((2 * z - 1) / 3 + 1) = 2 * (z + 1) := by have := h.1 trivial; omega
    calc 3 ^ (n + 1) * (app (List.replicate n true) ((2 * z - 1) / 3) + 1)
        = 3 * (3 ^ n * (app (List.replicate n true) ((2 * z - 1) / 3) + 1)) := by ring
      _ = 3 * (2 ^ n * ((2 * z - 1) / 3 + 1)) := by rw [ih]
      _ = 2 ^ n * (3 * ((2 * z - 1) / 3 + 1)) := by ring
      _ = 2 ^ (n + 1) * (z + 1) := by rw [h3]; ring

/-! ## (B) Admissible residue classes (Wirsching) -/

/-- For every word `w` and every residue `ρ` mod `3^M` there is a class `κ` mod
`3^(M + ℓ)` (`ℓ` the number of odd backward steps in `w`) such that `w` is admissible at
every `z ≡ κ` and its output is `≡ ρ (mod 3^M)`. -/
theorem adm_class (M ρ : ℕ) : ∀ w : List Bool, ∃ κ, ∀ z, z ≡ κ [MOD 3 ^ (M + w.count true)] →
    Adm w z ∧ app w z ≡ ρ [MOD 3 ^ M]
  | [] => ⟨ρ, fun z hz => ⟨trivial, by simpa [app] using hz⟩⟩
  | false :: w => by
    obtain ⟨κ', hκ'⟩ := adm_class M ρ w
    set N := M + w.count true
    have hodd : 3 ^ N % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 2 * ((3 ^ N + 1) / 2) = 3 ^ N + 1 := by omega
    refine ⟨κ' * ((3 ^ N + 1) / 2), fun z hz => ?_⟩
    have hc : (false :: w).count true = w.count true := by simp
    rw [hc] at hz
    have hz2 : 2 * z ≡ κ' [MOD 3 ^ N] := by
      calc 2 * z ≡ 2 * (κ' * ((3 ^ N + 1) / 2)) [MOD 3 ^ N] := hz.mul_left 2
        _ = κ' + 3 ^ N * κ' := by
          rw [mul_left_comm, h2]; ring
        _ ≡ κ' [MOD 3 ^ N] := by simp [Nat.ModEq]
    obtain ⟨h1, h2⟩ := hκ' _ hz2
    exact ⟨⟨by simp, h1⟩, h2⟩
  | true :: w => by
    obtain ⟨κ', hκ'⟩ := adm_class M ρ w
    set N := M + w.count true
    have hodd : 3 ^ (N + 1) % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 2 * ((3 ^ (N + 1) + 1) / 2) = 3 ^ (N + 1) + 1 := by omega
    refine ⟨(3 * κ' + 1) * ((3 ^ (N + 1) + 1) / 2), fun z hz => ?_⟩
    have hc : M + (true :: w).count true = N + 1 := by simp [N]; ring
    rw [hc] at hz
    have hz2 : 2 * z ≡ 3 * κ' + 1 [MOD 3 ^ (N + 1)] := by
      calc 2 * z ≡ 2 * ((3 * κ' + 1) * ((3 ^ (N + 1) + 1) / 2)) [MOD 3 ^ (N + 1)] :=
            hz.mul_left 2
        _ = (3 * κ' + 1) + 3 ^ (N + 1) * (3 * κ' + 1) := by
          rw [mul_left_comm, h2]; ring
        _ ≡ 3 * κ' + 1 [MOD 3 ^ (N + 1)] := by simp [Nat.ModEq]
    have hz3 : 2 * z ≡ 3 * κ' + 1 [MOD 3] :=
      Nat.ModEq.of_dvd (dvd_pow_self 3 (by omega)) hz2
    have hzm : z % 3 = 2 := by
      unfold Nat.ModEq at hz3; omega
    have he : 3 * ((2 * z - 1) / 3) + 1 = 2 * z := by omega
    have hx : (2 * z - 1) / 3 ≡ κ' [MOD 3 ^ N] := by
      rw [← he, pow_succ'] at hz2
      exact Nat.ModEq.mul_left_cancel' (by norm_num) (Nat.ModEq.add_right_cancel' 1 hz2)
    obtain ⟨h1, h2⟩ := hκ' _ hx
    exact ⟨⟨fun _ => hzm, h1⟩, h2⟩

lemma kstepT_pow_mul (k x : ℕ) : kstepT^[k] (2 ^ k * x) = x := by
  have := kstepT_app (List.replicate k false) x (adm_rep_false k x)
  rwa [app_rep_false, List.length_replicate] at this

/-! ## (A) The translation word (Monks et al., eq. (3.1)) -/

/-- The block `s₁ = P0^f, P1, P0^f, P1^f, P0^2` (application order). With `f + 1 = φ(b)` it
acts on `ZMod b` as `x ↦ x + 1` (`blk_mod`). -/
def blk (f : ℕ) : List Bool :=
  List.replicate f false ++ ([true] ++ (List.replicate f false ++
    (List.replicate f true ++ [false, false])))

lemma true_mem_blk (f : ℕ) : true ∈ blk f := by simp [blk]

lemma blk_mod {b f : ℕ} (h2 : (2 : ZMod b) ^ (f + 1) = 1) (h3 : (3 : ZMod b) ^ (f + 1) = 1)
    (z : ℕ) (h : Adm (blk f) z) : ((app (blk f) z : ℕ) : ZMod b) = z + 1 := by
  simp only [blk, adm_append, app_append, app_rep_false] at h ⊢
  obtain ⟨-, hT, -, hR, -⟩ := h
  have hz1 : (2 ^ f * z) % 3 = 2 := hT.1 rfl
  have e2 : 3 * ((2 * (2 ^ f * z) - 1) / 3) + 1 = 2 * (2 ^ f * z) := by omega
  have happ1 : app [true] (2 ^ f * z) = (2 * (2 ^ f * z) - 1) / 3 := rfl
  rw [happ1] at hR ⊢
  generalize (2 * (2 ^ f * z) - 1) / 3 = z2 at hR e2 ⊢
  have e4 := app_rep_true f _ hR
  generalize app (List.replicate f true) (2 ^ f * z2) = z4 at e4 ⊢
  have happ2 : app [false, false] z4 = 2 * (2 * z4) := rfl
  rw [happ2]
  have c2 : (3 : ZMod b) * z2 + 1 = 2 * (2 ^ f * z) := by
    exact_mod_cast congrArg (Nat.cast (R := ZMod b)) e2
  have c4 : (3 : ZMod b) ^ f * (z4 + 1) = 2 ^ f * (2 ^ f * z2 + 1) := by
    exact_mod_cast congrArg (Nat.cast (R := ZMod b)) e4
  rw [pow_succ'] at h2 h3
  push_cast
  linear_combination (-4 * ((z4 : ZMod b) + 1)) * h3 + 12 * c4 +
    (3 * (z2 : ZMod b) * (2 * 2 ^ f + 1) + 6 + z) * h2 + c2

/-- `bp f j = s₁^j`. -/
def bp (f : ℕ) : ℕ → List Bool
  | 0 => []
  | j + 1 => blk f ++ bp f j

lemma bp_add (f : ℕ) : ∀ i j, bp f (i + j) = bp f i ++ bp f j
  | 0, j => by simp [bp]
  | i + 1, j => by
    rw [show i + 1 + j = (i + j) + 1 by omega, bp, bp, bp_add f i j, List.append_assoc]

lemma true_mem_bp (f : ℕ) {j : ℕ} (hj : 1 ≤ j) : true ∈ bp f j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp [bp, true_mem_blk]

lemma bp_mod {b f : ℕ} (h2 : (2 : ZMod b) ^ (f + 1) = 1) (h3 : (3 : ZMod b) ^ (f + 1) = 1) :
    ∀ (j z : ℕ), Adm (bp f j) z → ((app (bp f j) z : ℕ) : ZMod b) = z + j
  | 0, z, _ => by simp [bp, app]
  | j + 1, z, h => by
    rw [bp, adm_append] at h
    rw [bp, app_append, bp_mod h2 h3 j _ h.2, blk_mod h2 h3 z h.1]
    push_cast; ring

lemma zmod_pows {b : ℕ} (hb : Nat.Coprime b 6) :
    (2 : ZMod b) ^ (Nat.totient b - 1 + 1) = 1 ∧ (3 : ZMod b) ^ (Nat.totient b - 1 + 1) = 1 := by
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hb
    · exact h
  rw [Nat.sub_add_cancel (Nat.totient_pos.2 hb0)]
  have c2 : Nat.Coprime 2 b := (Nat.Coprime.coprime_dvd_right (by norm_num) hb).symm
  have c3 : Nat.Coprime 3 b := (Nat.Coprime.coprime_dvd_right (by norm_num) hb).symm
  have e2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient c2)
  have e3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient c3)
  push_cast at e2 e3
  exact ⟨e2, e3⟩

/-! ## (D) A predecessor of `m` that is divisible by `b` -/

theorem exists_zero_mod {b : ℕ} (hb : Nat.Coprime b 6) (m : ℕ) (hm : m % 3 ≠ 0) :
    ∃ y0 K, y0 % 3 ≠ 0 ∧ ((y0 : ℕ) : ZMod b) = 0 ∧ kstepT^[K] y0 = m := by
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hb
    · exact h
  obtain ⟨h2, h3⟩ := zmod_pows hb
  set f := Nat.totient b - 1
  obtain ⟨κ, hκ⟩ := adm_class 0 0 (bp f (b + 1))
  have hκu : κ % 3 ≠ 0 := adm_unit _ κ (hκ κ rfl).1 (true_mem_bp f (by omega))
  obtain ⟨k, hk⟩ := hit_unit _ κ m hκu hm
  have hadm := (hκ _ hk).1
  set c := 2 ^ k * m
  have hlt : c % b < b := Nat.mod_lt c hb0
  set j := b - c % b
  rw [show b + 1 = j + (b + 1 - j) by omega, bp_add, adm_append] at hadm
  obtain ⟨hA, hR⟩ := hadm
  refine ⟨app (bp f j) c, k + (bp f j).length, ?_, ?_, ?_⟩
  · exact adm_unit _ _ hR (true_mem_bp f (by omega))
  · rw [bp_mod h2 h3 j c hA]
    have hdvd : b ∣ c + j := by
      refine ⟨c / b + 1, ?_⟩
      have e1 := Nat.div_add_mod c b
      have e2 : j = b - c % b := rfl
      clear_value c j
      generalize c % b = r at e1 e2 hlt
      generalize c / b = Q at e1 ⊢
      rw [mul_add, mul_one]
      omega
    obtain ⟨q, hq⟩ := hdvd
    have : ((c + j : ℕ) : ZMod b) = 0 := by rw [hq]; push_cast; simp
    exact_mod_cast this
  · rw [Function.iterate_add_apply, kstepT_app _ _ hA, kstepT_pow_mul]

/-! ## (E) The odd-modulus lemma -/

theorem exists_odd_mod {b : ℕ} (hb : Nat.Coprime b 6) (m : ℕ) (hm : m % 3 ≠ 0)
    (L β ρ B : ℕ) : ∃ z K, B ≤ z ∧ z ≡ β [MOD b] ∧ z ≡ ρ [MOD 3 ^ L] ∧ kstepT^[K] z = m := by
  obtain ⟨y0, K0, hy03, hy0b, hK0⟩ := exists_zero_mod hb m hm
  obtain ⟨h2, h3⟩ := zmod_pows hb
  set f := Nat.totient b - 1
  set J := β % b + b
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hb
    · exact h
  have hJ : 1 ≤ J := by omega
  set V := bp f J
  obtain ⟨κ, hκ⟩ := adm_class L ρ V
  have hκu : κ % 3 ≠ 0 := adm_unit _ κ (hκ κ rfl).1 (true_mem_bp f hJ)
  set N := L + V.count true
  obtain ⟨k0, hk0⟩ := hit_unit N κ y0 hκu hy03
  set t := V.length + B
  set k := k0 + t * Nat.totient (3 ^ N)
  have hk : 2 ^ k * y0 ≡ κ [MOD 3 ^ N] := ((two_pow_period N k0 t).mul_right y0).trans hk0
  obtain ⟨hadm, hmod⟩ := hκ _ hk
  refine ⟨app V (2 ^ k * y0), K0 + (k + V.length), ?_, ?_, hmod, ?_⟩
  · have hle := iterate_kstepT_le (app V (2 ^ k * y0)) V.length
    rw [kstepT_app _ _ hadm] at hle
    have hT : 1 ≤ Nat.totient (3 ^ N) := Nat.totient_pos.2 (by positivity)
    have hkt : V.length + B ≤ k := by
      have : t ≤ t * Nat.totient (3 ^ N) := Nat.le_mul_of_pos_right t hT
      omega
    have hB : B < 2 ^ B := Nat.lt_two_pow_self
    have hy1 : 1 ≤ y0 := by omega
    have : 2 ^ V.length * B ≤ 2 ^ k * y0 := by
      calc 2 ^ V.length * B ≤ 2 ^ V.length * 2 ^ B := Nat.mul_le_mul_left _ hB.le
        _ = 2 ^ (V.length + B) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkt
        _ ≤ 2 ^ k * y0 := Nat.le_mul_of_pos_right _ hy1
    exact Nat.le_of_mul_le_mul_left (this.trans hle) (by positivity)
  · have hz := bp_mod h2 h3 J _ hadm
    push_cast at hz
    rw [hy0b, mul_zero, zero_add] at hz
    have : app V (2 ^ k * y0) ≡ J [MOD b] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hz
    refine this.trans ?_
    show (β % b + b) % b = β % b
    rw [Nat.add_mod_right, Nat.mod_mod]
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, kstepT_app _ _ hadm,
      kstepT_pow_mul, hK0]

/-! ## (F) The key lemma for an arbitrary modulus -/

/-- **Key lemma.** If `3 ∤ m`, then every residue class `a mod d` contains arbitrarily large
`T`-ancestors of `m` (`T = kstepT`). -/
theorem exists_pred_mod {m : ℕ} (hm : m % 3 ≠ 0) (a d B : ℕ) (hd : 0 < d) :
    ∃ y K, B ≤ y ∧ y % d = a % d ∧ kstepT^[K] y = m := by
  obtain ⟨n, d1, hd1odd, hd⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  have hd1 : d1 ≠ 0 := by rintro rfl; simp at hd1odd
  obtain ⟨μ, b, hb3, hd1e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd1 3 (by norm_num)
  have hbodd : Odd b := Nat.Odd.of_mul_right (hd1e ▸ hd1odd)
  have c3b : Nat.Coprime 3 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3
  have hb6 : Nat.Coprime b 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hbodd) c3b.symm
  set r := a % 2 ^ n
  set q := a / 2 ^ n
  set s := oddCount n r
  set c := kstepT^[n] r
  obtain ⟨z, K, hzB, hzb, hz3, hzK⟩ :=
    exists_odd_mod hb6 m hm (s + μ) (c + 3 ^ s * q) (c + 3 ^ s * q) (c + 2 ^ n * B)
  have hzZ : z ≡ c + 3 ^ s * q [MOD 3 ^ (s + μ) * b] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow_left _ c3b)).1 ⟨hz3, hzb⟩
  rw [pow_add, mul_assoc] at hzZ
  have hzc : z ≡ c [MOD 3 ^ s] := by
    refine (Nat.ModEq.of_mul_right _ hzZ).trans ?_
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  obtain ⟨t, ht⟩ : 3 ^ s ∣ z - c := (Nat.modEq_iff_dvd' (by omega)).1 hzc.symm
  have hz : z = 3 ^ s * t + c := Nat.eq_add_of_sub_eq (by omega) ht
  have htq : t ≡ q [MOD 3 ^ μ * b] := by
    rw [hz, add_comm] at hzZ
    exact Nat.ModEq.mul_left_cancel' (by positivity) (Nat.ModEq.add_left_cancel' c hzZ)
  have hy : kstepT^[n] (2 ^ n * t + r) = z := by
    rw [iterate_affine n le_rfl, Nat.sub_self, pow_zero, one_mul, hz]
  refine ⟨2 ^ n * t + r, K + n, ?_, ?_, ?_⟩
  · have hle := iterate_kstepT_le (2 ^ n * t + r) n
    rw [hy] at hle
    exact Nat.le_of_mul_le_mul_left (a := B) (c := 2 ^ n) (by omega) (by positivity)
  · show 2 ^ n * t + r ≡ a [MOD d]
    have ha : 2 ^ n * q + r = a := Nat.div_add_mod a (2 ^ n)
    rw [hd, hd1e]
    calc 2 ^ n * t + r ≡ 2 ^ n * q + r [MOD 2 ^ n * (3 ^ μ * b)] :=
          (htq.mul_left' (2 ^ n)).add_right r
      _ = a := ha
  · rw [Function.iterate_add_apply, hy, hzK]

/-! ## (0), (1) Elementary facts about `step` -/

lemma step_iterate_one : ∀ j, step^[j] 1 = 1 ∨ step^[j] 1 = 4 ∨ step^[j] 1 = 2
  | 0 => Or.inl rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    rcases step_iterate_one j with h | h | h <;> rw [h] <;> decide

/-- Every point of an orbit that reaches `1` also reaches `1`. -/
theorem ReachesOne.iterate {n : ℕ} (h : ReachesOne n) (k : ℕ) : ReachesOne (step^[k] n) := by
  obtain ⟨k0, hk0⟩ := h
  rcases le_or_gt k k0 with hk | hk
  · exact ⟨k0 - k, by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk, hk0]⟩
  · have e : step^[k] n = step^[k - k0] 1 := by
      rw [← hk0, ← Function.iterate_add_apply, Nat.sub_add_cancel hk.le]
    rw [e]
    rcases step_iterate_one (k - k0) with h | h | h <;> rw [h]
    exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩]

/-- Every positive orbit contains a point not divisible by `3`. -/
theorem exists_mod_three_ne (x : ℕ) (hx : 1 ≤ x) : ∃ i, step^[i] x % 3 ≠ 0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h3 : x % 3 = 0
    · rcases Nat.mod_two_eq_zero_or_one x with h2 | h2
      · obtain ⟨i, hi⟩ := ih (x / 2) (by omega) (by omega)
        exact ⟨i + 1, by rw [Function.iterate_succ_apply, step_even h2]; exact hi⟩
      · exact ⟨1, by rw [Function.iterate_one, step_odd h2]; omega⟩
    · exact ⟨0, h3⟩

/-! ## (G) Assembly -/

/-- Every positive orbit merges with the orbit of some positive member of `{a + d n}`. -/
theorem exists_merge (a d : ℕ) (hd : 1 ≤ d) (x : ℕ) (hx : 1 ≤ x) :
    ∃ n i j, 1 ≤ a + d * n ∧ step^[j] (a + d * n) = step^[i] x := by
  obtain ⟨i, hi⟩ := exists_mod_three_ne x hx
  obtain ⟨y, K, hyB, hya, hyK⟩ := exists_pred_mod hi a d (max a 1) (by omega)
  have hay : a ≤ y := le_trans (le_max_left _ _) hyB
  obtain ⟨q, hq⟩ : d ∣ y - a := (Nat.modEq_iff_dvd' hay).1 (show y ≡ a [MOD d] from hya).symm
  have hy : y = a + d * q := by rw [Nat.eq_add_of_sub_eq hay hq, add_comm]
  obtain ⟨j, -, hj⟩ := step_iterate_of_kstepT K y
  exact ⟨q, i, j, by omega, by rw [← hy, hj, hyK]⟩

/-- **Monks (2006), Theorem 1.1.** If the Collatz conjecture holds for every positive
integer of one arithmetic progression `{a + d n : n ≥ 0}` (`d ≥ 1`), then it holds. -/
theorem conjecture_of_arith_prog (a d : ℕ) (hd : 1 ≤ d)
    (h : ∀ n, 1 ≤ a + d * n → ReachesOne (a + d * n)) : Conjecture := by
  intro x hx
  obtain ⟨n, i, j, h1, hij⟩ := exists_merge a d hd x hx
  refine ReachesOne.of_iterate (k := i) ?_
  rw [← hij]
  exact ReachesOne.iterate (h n h1) j

/-- The Collatz conjecture is equivalent to its restriction to any arithmetic progression. -/
theorem conjecture_iff_arith_prog (a d : ℕ) (hd : 1 ≤ d) :
    Conjecture ↔ ∀ n, 1 ≤ a + d * n → ReachesOne (a + d * n) :=
  ⟨fun hC _ hn => hC _ hn, conjecture_of_arith_prog a d hd⟩

/-! ## (4) Divergent orbits and cycles -/

/-- **Divergent orbits.** If some positive orbit is unbounded, then so is the orbit of some
member of every arithmetic progression. -/
theorem exists_unbounded_of_unbounded (a d : ℕ) (hd : 1 ≤ d)
    (h : ∃ x, 1 ≤ x ∧ ¬ BddAbove (Set.range fun k => step^[k] x)) :
    ∃ n, ¬ BddAbove (Set.range fun k => step^[k] (a + d * n)) := by
  obtain ⟨x, hx, hunb⟩ := h
  obtain ⟨n, i, j, -, hij⟩ := exists_merge a d hd x hx
  refine ⟨n, fun ⟨C, hC⟩ => hunb ⟨max ((Finset.range i).sup fun k => step^[k] x) C, ?_⟩⟩
  rintro _ ⟨k, rfl⟩
  dsimp only
  rcases lt_or_ge k i with hk | hk
  · exact le_max_of_le_left (Finset.le_sup (f := fun k => step^[k] x) (Finset.mem_range.2 hk))
  · apply le_max_of_le_right
    have e : step^[k] x = step^[k - i + j] (a + d * n) := by
      rw [Function.iterate_add_apply, hij, ← Function.iterate_add_apply, Nat.sub_add_cancel hk]
    rw [e]
    exact hC ⟨k - i + j, rfl⟩

/-- **Orbits not reaching `1`.** A positive integer that never reaches `1` merges with a
member of the progression that never reaches `1` either. -/
theorem exists_not_reachesOne (a d : ℕ) (hd : 1 ≤ d) (x : ℕ) (hx : 1 ≤ x)
    (hn : ¬ ReachesOne x) :
    ∃ n i j, 1 ≤ a + d * n ∧ step^[j] (a + d * n) = step^[i] x ∧ ¬ ReachesOne (a + d * n) := by
  obtain ⟨n, i, j, h1, hij⟩ := exists_merge a d hd x hx
  refine ⟨n, i, j, h1, hij, fun hR => hn (ReachesOne.of_iterate (k := i) ?_)⟩
  rw [← hij]
  exact ReachesOne.iterate hR j

/-- **Cycles.** Every cycle of positive integers (in particular every nontrivial one) is
entered by the orbit of some positive member of every arithmetic progression. -/
theorem exists_reaches_cycle (a d : ℕ) (hd : 1 ≤ d) (x : ℕ) (hx : 1 ≤ x) (p : ℕ) (hp : 1 ≤ p)
    (hc : step^[p] x = x) : ∃ n j, 1 ≤ a + d * n ∧ step^[j] (a + d * n) = x := by
  obtain ⟨n, i, j, h1, hij⟩ := exists_merge a d hd x hx
  have hpi : step^[p * i] x = x := by rw [Function.iterate_mul]; exact Function.iterate_fixed hc i
  refine ⟨n, p * i - i + j, h1, ?_⟩
  rw [Function.iterate_add_apply, hij, ← Function.iterate_add_apply,
    Nat.sub_add_cancel (Nat.le_mul_of_pos_left i hp), hpi]

end Collatz.MonksAP

/-! ## Axioms -/

/--
info: 'Collatz.MonksAP.exists_pred_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.exists_pred_mod

/--
info: 'Collatz.MonksAP.conjecture_of_arith_prog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.conjecture_of_arith_prog

/--
info: 'Collatz.MonksAP.conjecture_iff_arith_prog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.conjecture_iff_arith_prog

/--
info: 'Collatz.MonksAP.exists_unbounded_of_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.exists_unbounded_of_unbounded

/--
info: 'Collatz.MonksAP.exists_not_reachesOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.exists_not_reachesOne

/--
info: 'Collatz.MonksAP.exists_reaches_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.MonksAP.exists_reaches_cycle
