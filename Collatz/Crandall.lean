import Collatz.Cycle

/-!
# Many integers reach 1 (a Crandall-type lower bound)

Going backwards from `1`: if `m` is odd, reaches `1`, and `2^a m ≡ 1 (mod 3)`, then
`k = (2^a m - 1) / 3` is odd and reaches `1` (`step k = 2^a m`). Reducing mod `9`, for every odd
`m` with `3 ∤ m` there are two exponents `3 ≤ a ≤ 8` for which `3 ∤ k` as well (`e1`, `e2`,
checked by `decide`), so the backward tree branches forever. A node at depth `d` is at most
`86^d` (since `2^8 / 3 < 86`), and since `3k + 1 = 2^a m` with `m` odd determines `m` and `a`,
distinct branch choices give distinct numbers. Hence

  `2^d ≤ #{n ≤ 86^d | ReachesOne n}`  (`card_reachesOne_ge`),

and `N^c ≤ 2 #{n ≤ N | ReachesOne n}` with `c = log 2 / log 86 ≈ 0.156`
(`card_reachesOne_ge_rpow`). (Crandall 1978 proved such a bound for some `c > 0`; Krasikov and
Lagarias reached `c = 0.84` with computer-assisted inequalities.)
-/

namespace Collatz

open Finset

/-! ## The backward step -/

/-- The backward odd predecessor `(2^a m - 1) / 3`. -/
def child (m a : ℕ) : ℕ := (2 ^ a * m - 1) / 3

/-- Two exponents per residue of `m` mod `9`. -/
def e1 (r : ℕ) : ℕ := match r with
  | 1 => 4 | 2 => 3 | 4 => 6 | 5 => 3 | 7 => 4 | _ => 5
def e2 (r : ℕ) : ℕ := match r with
  | 1 => 8 | 2 => 7 | 4 => 8 | 5 => 5 | 7 => 6 | _ => 7

theorem exponents_ok : ∀ r < 9, r % 3 ≠ 0 →
    ((2 ^ e1 r * r) % 9 = 4 ∨ (2 ^ e1 r * r) % 9 = 7) ∧
    ((2 ^ e2 r * r) % 9 = 4 ∨ (2 ^ e2 r * r) % 9 = 7) ∧
    e1 r ≠ e2 r ∧ 1 ≤ e1 r ∧ e1 r ≤ 8 ∧ 1 ≤ e2 r ∧ e2 r ≤ 8 := by decide

lemma pow_mul_mod_nine (a m : ℕ) : (2 ^ a * m) % 9 = (2 ^ a * (m % 9)) % 9 := by
  rw [Nat.mul_mod, Nat.mul_mod (2 ^ a) (m % 9), Nat.mod_mod]

lemma ReachesOne.pow_mul {m : ℕ} (h : ReachesOne m) : ∀ a, ReachesOne (2 ^ a * m)
  | 0 => by simpa using h
  | a + 1 => by
    apply ReachesOne.of_step
    rw [step_even (by rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc]; exact Nat.mul_mod_right 2 _)]
    have : 2 ^ (a + 1) * m / 2 = 2 ^ a * m := by
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [this]; exact ReachesOne.pow_mul h a

/-- Properties of a good child. -/
lemma child_spec {m a : ℕ} (ha : 1 ≤ a) (hm : ReachesOne m)
    (h9 : (2 ^ a * m) % 9 = 4 ∨ (2 ^ a * m) % 9 = 7) :
    3 * child m a + 1 = 2 ^ a * m ∧ child m a % 2 = 1 ∧ child m a % 3 ≠ 0 ∧
      ReachesOne (child m a) := by
  have heven : (2 ^ a * m) % 2 = 0 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [pow_succ, mul_comm (2 ^ b) 2, mul_assoc]; simp
  have h3 : 3 * child m a + 1 = 2 ^ a * m := by unfold child; omega
  have hodd : child m a % 2 = 1 := by omega
  refine ⟨h3, hodd, by unfold child; omega, ?_⟩
  apply ReachesOne.of_step
  rw [step_odd hodd, h3]
  exact hm.pow_mul a

/-! ## The tree -/

/-- The exponent chosen at node `m` for branch `b`. -/
def expo (m : ℕ) (b : Bool) : ℕ := if b then e1 (m % 9) else e2 (m % 9)

/-- The node reached by the branch choices `l` (most recent first). -/
def node : List Bool → ℕ
  | [] => 1
  | b :: l => child (node l) (expo (node l) b)

lemma expo_spec {m : ℕ} (hm : m % 3 ≠ 0) (b : Bool) :
    ((2 ^ expo m b * m) % 9 = 4 ∨ (2 ^ expo m b * m) % 9 = 7) ∧ 1 ≤ expo m b ∧ expo m b ≤ 8 := by
  have hr : m % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hr3 : m % 9 % 3 ≠ 0 := by omega
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := exponents_ok (m % 9) hr hr3
  rw [pow_mul_mod_nine]
  cases b
  · exact ⟨h2, h6, h7⟩
  · exact ⟨h1, h4, h5⟩

theorem node_spec : ∀ l : List Bool,
    node l % 2 = 1 ∧ node l % 3 ≠ 0 ∧ ReachesOne (node l) ∧ node l ≤ 86 ^ l.length
  | [] => ⟨rfl, by decide, reachesOne_one, by simp [node]⟩
  | b :: l => by
    obtain ⟨-, h3, hr, hle⟩ := node_spec l
    obtain ⟨h9, ha1, ha8⟩ := expo_spec h3 b
    obtain ⟨e, hodd, hmod3, hreach⟩ := child_spec ha1 hr h9
    refine ⟨hodd, hmod3, hreach, ?_⟩
    simp only [node, List.length_cons, pow_succ]
    have h256 : 2 ^ expo (node l) b ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) ha8
    have : 2 ^ expo (node l) b * node l ≤ 256 * node l := Nat.mul_le_mul_right _ h256
    generalize child (node l) (expo (node l) b) = k at e ⊢
    generalize 2 ^ expo (node l) b * node l = N at e this
    nlinarith

/-- `2^a m = 2^b m'` with `m, m'` odd forces `a = b` and `m = m'`. -/
lemma pow_mul_odd_inj : ∀ {a b m m' : ℕ}, m % 2 = 1 → m' % 2 = 1 →
    2 ^ a * m = 2 ^ b * m' → a = b ∧ m = m'
  | 0, 0, m, m', _, _, h => ⟨rfl, by simpa using h⟩
  | 0, b + 1, m, m', hm, _, h => by
    rw [pow_zero, one_mul, pow_succ, mul_comm (2 ^ b) 2, mul_assoc] at h
    omega
  | a + 1, 0, m, m', _, hm', h => by
    rw [pow_zero, one_mul, pow_succ, mul_comm (2 ^ a) 2, mul_assoc] at h
    omega
  | a + 1, b + 1, m, m', hm, hm', h => by
    rw [pow_succ, pow_succ, mul_comm (2 ^ a) 2, mul_comm (2 ^ b) 2, mul_assoc, mul_assoc] at h
    obtain ⟨h1, h2⟩ := pow_mul_odd_inj (a := a) (b := b) hm hm' (by omega)
    exact ⟨by rw [h1], h2⟩

theorem node_inj : ∀ {l l' : List Bool}, l.length = l'.length → node l = node l' → l = l'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨hm, h3, hr, -⟩ := node_spec l
    obtain ⟨hm', h3', hr', -⟩ := node_spec l'
    obtain ⟨h9, ha1, -⟩ := expo_spec h3 b
    obtain ⟨h9', ha1', -⟩ := expo_spec h3' b'
    have e := (child_spec ha1 hr h9).1
    have e' := (child_spec ha1' hr' h9').1
    simp only [node] at h
    rw [h] at e
    obtain ⟨hexp, hnode⟩ := pow_mul_odd_inj hm hm' (e.symm.trans e')
    have hl := node_inj hlen hnode
    subst hl
    have hb : b = b' := by
      have := (exponents_ok (node l % 9) (Nat.mod_lt _ (by norm_num)) (by omega)).2.2.1
      cases b <;> cases b' <;> simp_all [expo]
    rw [hb]

/-! ## Counting -/

open Classical in
/-- **At least `2^d` integers `n ≤ 86^d` reach `1`.** -/
theorem card_reachesOne_ge (d : ℕ) :
    2 ^ d ≤ ((range (86 ^ d + 1)).filter ReachesOne).card := by
  have hinj : Function.Injective (fun v : Fin d → Bool => node (List.ofFn v)) := by
    intro v w h
    exact List.ofFn_injective (node_inj (by simp) h)
  calc 2 ^ d = (univ.image (fun v : Fin d → Bool => node (List.ofFn v))).card := by
        rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
    _ ≤ _ := by
        apply card_le_card
        intro n hn
        simp only [mem_image, mem_univ, true_and] at hn
        obtain ⟨v, rfl⟩ := hn
        obtain ⟨-, -, hr, hle⟩ := node_spec (List.ofFn v)
        simp only [List.length_ofFn] at hle
        simp only [mem_filter, mem_range]
        exact ⟨by omega, hr⟩

open Classical in
/-- **`N^c ≤ 2 #{n ≤ N | n reaches 1}` with `c = log 2 / log 86`.** -/
theorem card_reachesOne_ge_rpow (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.log 2 / Real.log 86) ≤
      2 * (((range (N + 1)).filter ReachesOne).card : ℝ) := by
  set d := Nat.log 86 N
  have hlo : 86 ^ d ≤ N := Nat.pow_log_le_self 86 (by omega)
  have hhi : N < 86 ^ (d + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hcard : 2 ^ d ≤ ((range (N + 1)).filter ReachesOne).card :=
    (card_reachesOne_ge d).trans (card_le_card (by
      intro n hn; simp only [mem_filter, mem_range] at hn ⊢; exact ⟨by omega, hn.2⟩))
  have h86 : (0 : ℝ) < Real.log 86 := Real.log_pos (by norm_num)
  have hc : 0 ≤ Real.log 2 / Real.log 86 := div_nonneg (Real.log_nonneg (by norm_num)) h86.le
  have key : ((86 : ℝ) ^ (d + 1)) ^ (Real.log 2 / Real.log 86) = 2 ^ (d + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    rw [show Real.log 86 * (((d + 1 : ℕ) : ℝ) * (Real.log 2 / Real.log 86)) =
        ((d + 1 : ℕ) : ℝ) * Real.log 2 by field_simp]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc (N : ℝ) ^ (Real.log 2 / Real.log 86)
      ≤ ((86 : ℝ) ^ (d + 1)) ^ (Real.log 2 / Real.log 86) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi.le) hc
    _ = 2 * 2 ^ d := by rw [key, pow_succ]; ring
    _ ≤ 2 * (((range (N + 1)).filter ReachesOne).card : ℝ) := by
        have : ((2 : ℝ) ^ d) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) := by
          exact_mod_cast hcard
        linarith

end Collatz
