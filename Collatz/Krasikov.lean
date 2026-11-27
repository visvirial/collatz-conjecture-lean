import Collatz.Crandall

/-!
# At least `N^(3/7)` integers up to `N` reach 1 (Krasikov's exponent)

Let `U n = oddPart (3n + 1)` and let `D m x` be the odd `n ≤ x` with `U^j n = m` for some `j`.
For odd `m` with `3 ∤ m` and `m` not periodic under `U`, the children `(2^a m - 1)/3`
(`2 ≤ a ≤ 30`, prime to `3`) have pairwise disjoint sets `D (child) x` inside `D m x`.

With constants `C r` for the residues `r` mod `27` we prove, by induction on `x - m`,

  `C (m % 27) (x / m)^(3/7) ≤ 10^6 (2^30)^(3/7) #D m x`.

The induction step needs, for every residue `s` mod `81`,
`∑_a C (child % 27) (3 / 2^a)^(3/7) ≥ C (s % 27)`, which is certified by `decide +kernel` from
the rational bounds `(3/2^a)^(3/7) ≥ (G/D) (p/q)^a` (checked through seventh powers).
Krasikov (1989) obtained the exponent `3/7` from inequalities of this kind.
-/

namespace Collatz

open Finset

/-! ## The odd part and the backward map -/

/-- The odd part of `n` (with `oddPart 0 = 0`). -/
def oddPart (n : ℕ) : ℕ := if h : 0 < n ∧ n % 2 = 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

lemma oddPart_of_even {n : ℕ} (hpos : 0 < n) (h : n % 2 = 0) : oddPart n = oddPart (n / 2) := by
  rw [oddPart]; simp [hpos, h]

lemma oddPart_of_odd {n : ℕ} (h : n % 2 = 1) : oddPart n = n := by
  rw [oddPart]; simp [h]

lemma oddPart_pow_mul {m : ℕ} (hm : m % 2 = 1) : ∀ a, oddPart (2 ^ a * m) = m
  | 0 => by
    rw [pow_zero, one_mul, oddPart_of_odd hm]
  | a + 1 => by
    have hpos : 0 < 2 ^ (a + 1) * m := Nat.mul_pos (by positivity) (by omega)
    have heven : 2 ^ (a + 1) * m % 2 = 0 := by
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc]; exact Nat.mul_mod_right 2 _
    rw [oddPart_of_even hpos heven]
    have : 2 ^ (a + 1) * m / 2 = 2 ^ a * m := by
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [this, oddPart_pow_mul hm a]

lemma exists_eq_pow_mul_oddPart : ∀ n : ℕ, 0 < n → ∃ v, n = 2 ^ v * oddPart n ∧ oddPart n % 2 = 1
  | n => fun hn => by
    by_cases h : n % 2 = 0
    · obtain ⟨v, hv, ho⟩ := exists_eq_pow_mul_oddPart (n / 2) (by omega)
      refine ⟨v + 1, ?_, ?_⟩
      · rw [oddPart_of_even hn h, pow_succ, mul_comm (2 ^ v) 2, mul_assoc, ← hv]; omega
      · rw [oddPart_of_even hn h]; exact ho
    · refine ⟨0, ?_, ?_⟩
      · rw [oddPart_of_odd (by omega)]; simp
      · rw [oddPart_of_odd (by omega)]; omega
termination_by n => n
decreasing_by omega

/-- The backward map on odd numbers: `n ↦ oddPart (3n + 1)`. -/
def U (n : ℕ) : ℕ := oddPart (3 * n + 1)

lemma U_odd (n : ℕ) : U n % 2 = 1 := by
  obtain ⟨_, _, h⟩ := exists_eq_pow_mul_oddPart (3 * n + 1) (by omega); exact h

lemma U_of_eq {k a m : ℕ} (h : 3 * k + 1 = 2 ^ a * m) (hm : m % 2 = 1) : U k = m := by
  rw [U, h, oddPart_pow_mul hm]

lemma reachesOne_of_U {n : ℕ} (hn : n % 2 = 1) (h : ReachesOne (U n)) : ReachesOne n := by
  obtain ⟨v, hv, -⟩ := exists_eq_pow_mul_oddPart (3 * n + 1) (by omega)
  apply ReachesOne.of_step
  rw [step_odd hn, hv]
  exact h.pow_mul v

lemma reachesOne_of_U_iterate {m : ℕ} (hm : ReachesOne m) :
    ∀ j n, n % 2 = 1 → U^[j] n = m → ReachesOne n
  | 0, n, _, h => by rw [Function.iterate_zero_apply] at h; rw [h]; exact hm
  | j + 1, n, hn, h => by
    rw [Function.iterate_succ_apply] at h
    exact reachesOne_of_U hn (reachesOne_of_U_iterate hm j (U n) (U_odd n) h)

/-- `m` is not periodic under `U`. -/
def NP (m : ℕ) : Prop := ∀ j, 1 ≤ j → U^[j] m ≠ m

lemma U_iterate_comm (j n : ℕ) : U^[j] (U n) = U (U^[j] n) := by
  rw [← Function.iterate_succ_apply U j n, Function.iterate_succ_apply' U j n]

lemma NP_of_U {m c : ℕ} (hm : NP m) (hc : U c = m) : NP c := by
  intro j hj h
  apply hm j hj
  rw [← hc, U_iterate_comm, h]

lemma U_one : U 1 = 1 := by
  rw [U, show 3 * 1 + 1 = 2 ^ 2 * 1 by norm_num, oddPart_pow_mul (by norm_num)]

lemma NP_five : NP 5 := by
  have h5 : U 5 = 1 := by
    rw [U, show 3 * 5 + 1 = 2 ^ 4 * 1 by norm_num, oddPart_pow_mul (by norm_num)]
  have h1 : ∀ j, U^[j] 1 = 1 := fun j => Function.iterate_fixed U_one j
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply, h5, h1]
  omega

lemma NP_ne_one {m : ℕ} (hm : NP m) : m ≠ 1 := by
  rintro rfl; exact hm 1 le_rfl (by simpa using U_one)

/-! ## The sets `D m x` -/

open Classical in
/-- Odd `n ≤ x` whose backward orbit hits `m`. -/
noncomputable def D (m x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun n => n % 2 = 1 ∧ ∃ j, U^[j] n = m)

lemma mem_D {m x n : ℕ} : n ∈ D m x ↔ n ≤ x ∧ n % 2 = 1 ∧ ∃ j, U^[j] n = m := by
  classical
  simp [D]

lemma D_subset {m c x : ℕ} (hc : U c = m) : D c x ⊆ D m x := by
  intro n hn
  rw [mem_D] at hn ⊢
  obtain ⟨h1, h2, j, hj⟩ := hn
  exact ⟨h1, h2, j + 1, by rw [Function.iterate_succ_apply', hj, hc]⟩

lemma D_disjoint {m c c' x : ℕ} (hm : NP m) (hc : U c = m) (hc' : U c' = m) (hne : c ≠ c') :
    Disjoint (D c x) (D c' x) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [mem_D] at hn hn'
  obtain ⟨-, -, j, hj⟩ := hn
  obtain ⟨-, -, j', hj'⟩ := hn'
  -- WLOG j ≤ j'
  have key : ∀ {c c' j j'}, U c = m → U c' = m → c ≠ c' → U^[j] n = c → U^[j'] n = c' →
      j ≤ j' → False := by
    intro c c' j j' hc hc' hne hj hj' hle
    obtain ⟨k, rfl⟩ : ∃ k, j' = k + j := ⟨j' - j, by omega⟩
    rw [Function.iterate_add_apply, hj] at hj'
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact hne (by simpa using hj')
    · apply hm k hk
      calc U^[k] m = U^[k] (U c) := by rw [hc]
        _ = U (U^[k] c) := U_iterate_comm k c
        _ = m := by rw [hj', hc']
  rcases le_total j j' with h | h
  · exact key hc hc' hne hj hj' h
  · exact key hc' hc (Ne.symm hne) hj' hj h

lemma self_mem_D {m x : ℕ} (hm : m % 2 = 1) (hx : m ≤ x) : m ∈ D m x :=
  mem_D.2 ⟨hx, hm, 0, rfl⟩

lemma self_not_mem_D {m c x : ℕ} (hm : NP m) (hc : U c = m) : m ∉ D c x := by
  intro h
  rw [mem_D] at h
  obtain ⟨-, -, j, hj⟩ := h
  apply hm (j + 1) (by omega)
  rw [Function.iterate_succ_apply', hj, hc]

/-! ## The certificate -/

/-- Constants for the residues mod `27` (zero on multiples of `3`). -/
def KrC : List ℕ := [0, 1000000, 523299, 0, 704383, 476519, 0, 552044, 263008, 0, 641348, 495654,
  0, 442737, 742997, 0, 354052, 410103, 0, 705634, 328852, 0, 667194, 524284, 0, 389541, 289311]

def Cc (r : ℕ) : ℕ := KrC.getD r 0

/-- `p/q ≤ 2^(-3/7)` and `G/D ≤ 3^(3/7)`. -/
def KrP : ℕ := 742996
def KrQ : ℕ := 1000000
def KrG : ℕ := 1601327
def KrD : ℕ := 1000000
def KrA : ℕ := 30

def condB (s a : ℕ) : Prop := (2 ^ a * s) % 9 = 4 ∨ (2 ^ a * s) % 9 = 7

instance (s a : ℕ) : Decidable (condB s a) := by unfold condB; infer_instance

def chI (s a : ℕ) : ℕ := ((2 ^ a * s) % 81 - 1) / 3 % 27

def krTerm (s a : ℕ) : ℕ := if 2 ≤ a ∧ condB s a then Cc (chI s a) * KrG * KrP ^ a * KrQ ^ (KrA - a) else 0

theorem krCert : ∀ s < 81, s % 3 ≠ 0 → Cc (s % 27) * KrD * KrQ ^ KrA ≤ ∑ a ∈ range (KrA + 1), krTerm s a := by
  decide +kernel

theorem Cc_le : ∀ r < 27, Cc r ≤ 1000000 := by decide

theorem pq_bound : KrP ^ 7 * 8 ≤ KrQ ^ 7 := by decide +kernel
theorem GD_bound : KrG ^ 7 ≤ 27 * KrD ^ 7 := by decide +kernel

lemma condB_mod (m a : ℕ) : condB (m % 81) a ↔ condB m a := by
  unfold condB
  have : (2 ^ a * (m % 81)) % 9 = (2 ^ a * m) % 9 := by
    rw [Nat.mul_mod, show m % 81 % 9 = m % 9 by omega, ← Nat.mul_mod]
  rw [this]

lemma chI_mod {m a : ℕ} (h : condB m a) : chI (m % 81) a = child m a % 27 := by
  unfold chI child
  have e : (2 ^ a * (m % 81)) % 81 = (2 ^ a * m) % 81 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [e]
  unfold condB at h
  omega

/-! ## Real estimates -/

noncomputable def ce : ℝ := 3 / 7

lemma w_lower (a : ℕ) :
    (KrG / KrD : ℝ) * (KrP / KrQ : ℝ) ^ a ≤ ((3 : ℝ) / 2 ^ a) ^ ce := by
  have h1 : (0 : ℝ) ≤ (KrG / KrD : ℝ) * (KrP / KrQ : ℝ) ^ a := by positivity
  have h2 : (0 : ℝ) ≤ ((3 : ℝ) / 2 ^ a) ^ ce := by positivity
  refine (pow_le_pow_iff_left₀ h1 h2 (by norm_num : (7 : ℕ) ≠ 0)).1 ?_
  have e : (((3 : ℝ) / 2 ^ a) ^ ce) ^ (7 : ℕ) = ((3 : ℝ) / 2 ^ a) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ce]
    norm_num
  rw [e, mul_pow, ← pow_mul, mul_comm a 7, pow_mul]
  have hG : ((KrG / KrD : ℝ)) ^ 7 ≤ 27 := by
    rw [div_pow, div_le_iff₀ (by norm_num [KrD])]
    exact_mod_cast GD_bound
  have hp : ((KrP / KrQ : ℝ)) ^ 7 ≤ 1 / 8 := by
    rw [div_pow, div_le_iff₀ (by norm_num [KrQ])]
    have := pq_bound
    have : ((KrP : ℝ)) ^ 7 * 8 ≤ (KrQ : ℝ) ^ 7 := by exact_mod_cast this
    linarith
  calc (KrG / KrD : ℝ) ^ 7 * ((KrP / KrQ : ℝ) ^ 7) ^ a ≤ 27 * (1 / 8) ^ a :=
        mul_le_mul hG (pow_le_pow_left₀ (by positivity) hp a) (by positivity) (by norm_num)
    _ = ((3 : ℝ) / 2 ^ a) ^ 3 := by
        rw [div_pow, div_pow, one_pow, ← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul,
          mul_comm 3 a]
        norm_num [div_eq_mul_inv]

/-- The certificate as a real inequality at a node `m`. -/
lemma krCert_real {m : ℕ} (hm : m % 3 ≠ 0) :
    (Cc (m % 27) : ℝ) ≤ ∑ a ∈ (range (KrA + 1)).filter (fun a => 2 ≤ a ∧ condB m a),
      (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a) ^ ce := by
  have hc := krCert (m % 81) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [show m % 81 % 27 = m % 27 by omega] at hc
  have hcR : ((Cc (m % 27) * KrD * KrQ ^ KrA : ℕ) : ℝ) ≤ ((∑ a ∈ range (KrA + 1), krTerm (m % 81) a : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hcR
  have hpos : (0 : ℝ) < KrD * KrQ ^ KrA := by norm_num [KrD, KrQ]
  rw [sum_filter]
  calc (Cc (m % 27) : ℝ)
      = (Cc (m % 27) * KrD * KrQ ^ KrA) / (KrD * KrQ ^ KrA) := by
        rw [mul_assoc, mul_div_assoc, div_self hpos.ne', mul_one]
    _ ≤ (∑ a ∈ range (KrA + 1), (krTerm (m % 81) a : ℝ)) / (KrD * KrQ ^ KrA) :=
        div_le_div_of_nonneg_right hcR hpos.le
    _ = ∑ a ∈ range (KrA + 1), (krTerm (m % 81) a : ℝ) / (KrD * KrQ ^ KrA) := by rw [sum_div]
    _ ≤ _ := by
        refine sum_le_sum (fun a ha => ?_)
        have haA : a ≤ KrA := by simp at ha; omega
        unfold krTerm
        by_cases h : 2 ≤ a ∧ condB m a
        · have h' : 2 ≤ a ∧ condB (m % 81) a := ⟨h.1, (condB_mod m a).2 h.2⟩
          simp only [h'.1, h'.2, h.2, and_self, ↓reduceIte]
          rw [chI_mod h.2]
          push_cast
          have hw := w_lower a
          have hC : (0 : ℝ) ≤ Cc (child m a % 27) := by positivity
          calc (Cc (child m a % 27) : ℝ) * KrG * KrP ^ a * KrQ ^ (KrA - a) / (KrD * KrQ ^ KrA)
              = (Cc (child m a % 27) : ℝ) * ((KrG / KrD : ℝ) * (KrP / KrQ : ℝ) ^ a) := by
                rw [div_pow]
                have hq : (KrQ : ℝ) ^ KrA = (KrQ : ℝ) ^ (KrA - a) * (KrQ : ℝ) ^ a := by
                  rw [← pow_add, Nat.sub_add_cancel haA]
                rw [hq]
                have hQ0 : (KrQ : ℝ) ≠ 0 := by norm_num [KrQ]
                have hD0 : (KrD : ℝ) ≠ 0 := by norm_num [KrD]
                field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left hw hC
        · have h' : ¬ (2 ≤ a ∧ condB (m % 81) a) := fun h' => h ⟨h'.1, (condB_mod m a).1 h'.2⟩
          simp only [h, h', ↓reduceIte]; simp

/-! ## The induction -/

lemma child_props {m a : ℕ} (hm1 : m % 2 = 1) (hNP : NP m) (ha : 2 ≤ a)
    (hc : condB m a) :
    3 * child m a + 1 = 2 ^ a * m ∧ child m a % 2 = 1 ∧ child m a % 3 ≠ 0 ∧ U (child m a) = m ∧
      NP (child m a) ∧ m < child m a := by
  have heven : (2 ^ a * m) % 2 = 0 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [pow_succ, mul_comm (2 ^ b) 2, mul_assoc]; exact Nat.mul_mod_right 2 _
  unfold condB at hc
  have h3 : 3 * child m a + 1 = 2 ^ a * m := by unfold child; omega
  have hU : U (child m a) = m := U_of_eq h3 hm1
  have hm2 : 2 ≤ m := by have := NP_ne_one hNP; omega
  have h4 : 4 * m ≤ 2 ^ a * m :=
    Nat.mul_le_mul_right m (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  refine ⟨h3, by omega, by unfold child; omega, hU, NP_of_U hNP hU, by omega⟩

/-- `#D m x ≥ ∑ #D (child) x` over the good exponents. -/
lemma card_D_ge {m x : ℕ} (hm1 : m % 2 = 1) (hNP : NP m) :
    ∑ a ∈ (range (KrA + 1)).filter (fun a => 2 ≤ a ∧ condB m a), (D (child m a) x).card ≤
      (D m x).card := by
  classical
  set S := (range (KrA + 1)).filter (fun a => 2 ≤ a ∧ condB m a)
  have hprops : ∀ a ∈ S, 3 * child m a + 1 = 2 ^ a * m ∧ U (child m a) = m := by
    intro a ha
    simp only [S, mem_filter] at ha
    obtain ⟨h1, -, -, h2, -⟩ := child_props hm1 hNP ha.2.1 ha.2.2
    exact ⟨h1, h2⟩
  have hinj : ∀ a ∈ S, ∀ b ∈ S, child m a = child m b → a = b := by
    intro a ha b hb h
    have e1 := (hprops a ha).1
    have e2 := (hprops b hb).1
    rw [h] at e1
    have hmpos : 0 < m := by omega
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hmpos (e1.symm.trans e2))
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.2 (fun a ha => D_subset (hprops a ha).2))
  · intro a ha b hb hab
    exact D_disjoint hNP (hprops a ha).2 (hprops b hb).2 (fun h => hab (hinj a ha b hb h))

/-- The constant on the right. -/
noncomputable def KrBig : ℝ := 1000000 * ((2 : ℝ) ^ KrA) ^ ce

theorem main_bound (x : ℕ) : ∀ d m, x - m = d → m ≤ x → m % 2 = 1 → m % 3 ≠ 0 → NP m →
    (Cc (m % 27) : ℝ) * ((x : ℝ) / m) ^ ce ≤ KrBig * (D m x).card := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro m hd hmx hm1 hm3 hNP
  have hmpos : (0 : ℝ) < m := by have : 0 < m := by omega
                                 exact_mod_cast this
  have hce : (0 : ℝ) ≤ ce := by norm_num [ce]
  have hxm : (0 : ℝ) ≤ (x : ℝ) / m := by positivity
  have hcard1 : (1 : ℝ) ≤ (D m x).card := by
    have : 1 ≤ (D m x).card := card_pos.2 ⟨m, self_mem_D hm1 hmx⟩
    exact_mod_cast this
  have hC : (Cc (m % 27) : ℝ) ≤ 1000000 := by
    have := Cc_le (m % 27) (Nat.mod_lt _ (by norm_num)); exact_mod_cast this
  by_cases hsmall : x * 3 < 2 ^ KrA * m
  · -- base case: the ratio is below 2^KrA
    have hr : (x : ℝ) / m ≤ 2 ^ KrA := by
      rw [div_le_iff₀ hmpos]
      have : (x : ℝ) * 3 < 2 ^ KrA * m := by exact_mod_cast hsmall
      nlinarith
    have hp : ((x : ℝ) / m) ^ ce ≤ ((2 : ℝ) ^ KrA) ^ ce := Real.rpow_le_rpow hxm hr hce
    calc (Cc (m % 27) : ℝ) * ((x : ℝ) / m) ^ ce ≤ 1000000 * ((2 : ℝ) ^ KrA) ^ ce :=
          mul_le_mul hC hp (by positivity) (by norm_num)
      _ = KrBig * 1 := by rw [KrBig, mul_one]
      _ ≤ KrBig * (D m x).card := mul_le_mul_of_nonneg_left hcard1 (by unfold KrBig; positivity)
  · push Not at hsmall
    set S := (range (KrA + 1)).filter (fun a => 2 ≤ a ∧ condB m a)
    have hchild : ∀ a ∈ S, (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a) ^ ce * ((x : ℝ) / m) ^ ce ≤
        KrBig * (D (child m a) x).card := by
      intro a ha
      have ha' := ha
      simp only [S, mem_filter, mem_range] at ha'
      obtain ⟨h3, hc1, hc3, -, hcNP, hlt⟩ := child_props hm1 hNP ha'.2.1 ha'.2.2
      have hpa : 2 ^ a * m ≤ 2 ^ KrA * m :=
        Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hcx : child m a ≤ x := by omega
      have hIH := ih (x - child m a) (by omega) (child m a) rfl hcx hc1 hc3 hcNP
      have hcpos : (0 : ℝ) < child m a := by have : 0 < child m a := by omega
                                             exact_mod_cast this
      -- (3/2^a) (x/m) ≤ x / child
      have hratio : (3 : ℝ) / 2 ^ a * ((x : ℝ) / m) ≤ (x : ℝ) / child m a := by
        have h3R : (3 : ℝ) * child m a + 1 = 2 ^ a * m := by exact_mod_cast h3
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hcpos]
        have hx0 : (0 : ℝ) ≤ x := by positivity
        nlinarith
      calc (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a) ^ ce * ((x : ℝ) / m) ^ ce
          = (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a * ((x : ℝ) / m)) ^ ce := by
            rw [Real.mul_rpow (by positivity) hxm, mul_assoc]
        _ ≤ (Cc (child m a % 27) : ℝ) * ((x : ℝ) / child m a) ^ ce :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hratio hce) (by positivity)
        _ ≤ _ := hIH
    calc (Cc (m % 27) : ℝ) * ((x : ℝ) / m) ^ ce
        ≤ (∑ a ∈ S, (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a) ^ ce) * ((x : ℝ) / m) ^ ce :=
          mul_le_mul_of_nonneg_right (krCert_real hm3) (by positivity)
      _ = ∑ a ∈ S, (Cc (child m a % 27) : ℝ) * ((3 : ℝ) / 2 ^ a) ^ ce * ((x : ℝ) / m) ^ ce := by
          rw [sum_mul]
      _ ≤ ∑ a ∈ S, KrBig * (D (child m a) x).card := sum_le_sum hchild
      _ = KrBig * ((∑ a ∈ S, (D (child m a) x).card : ℕ) : ℝ) := by rw [← mul_sum]; push_cast; rfl
      _ ≤ KrBig * (D m x).card := by
          apply mul_le_mul_of_nonneg_left _ (by unfold KrBig; positivity)
          exact_mod_cast card_D_ge hm1 hNP

open Classical in
/-- **Krasikov's bound**: for some `κ > 0`, at least `κ N^(3/7)` integers `n ≤ N` reach `1`. -/
theorem card_reachesOne_ge_three_sevenths :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
      κ * (N : ℝ) ^ ((3 : ℝ) / 7) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) := by
  have h5 : ReachesOne 5 := ⟨5, rfl⟩
  have hK : 0 < KrBig := by unfold KrBig; positivity
  refine ⟨(Cc 5 : ℝ) / (KrBig * (5 : ℝ) ^ ((3 : ℝ) / 7)), by
    have : (0 : ℝ) < Cc 5 := by norm_num [Cc, KrC]
    positivity, fun N hN => ?_⟩
  have hmain := main_bound N (N - 5) 5 rfl hN (by norm_num) (by norm_num) NP_five
  rw [show (5 : ℕ) % 27 = 5 by norm_num] at hmain
  have hsub : D 5 N ⊆ (range (N + 1)).filter ReachesOne := by
    intro n hn
    rw [mem_D] at hn
    obtain ⟨h1, h2, j, hj⟩ := hn
    simp only [mem_filter, mem_range]
    exact ⟨by omega, reachesOne_of_U_iterate h5 j n h2 hj⟩
  have hcard : ((D 5 N).card : ℝ) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ ((3 : ℝ) / 7) := by positivity
  have e : ((N : ℝ) / (5 : ℕ)) ^ ce = (N : ℝ) ^ ((3 : ℝ) / 7) / (5 : ℝ) ^ ((3 : ℝ) / 7) := by
    rw [ce, Real.div_rpow (by positivity) (by norm_num)]; norm_num
  rw [e] at hmain
  calc (Cc 5 : ℝ) / (KrBig * (5 : ℝ) ^ ((3 : ℝ) / 7)) * (N : ℝ) ^ ((3 : ℝ) / 7)
      = ((Cc 5 : ℝ) * ((N : ℝ) ^ ((3 : ℝ) / 7) / (5 : ℝ) ^ ((3 : ℝ) / 7))) / KrBig := by
        field_simp
    _ ≤ (KrBig * (D 5 N).card) / KrBig := div_le_div_of_nonneg_right hmain hK.le
    _ = (D 5 N).card := by field_simp
    _ ≤ _ := hcard

end Collatz
