import Collatz.Krasikov

/-!
# The Syracuse valuation vector (Tao 2022, §1–§2, Lemma 6.2, Prop. 1.9 special case)

Reference: T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*,
Forum Math. Pi **10** (2022), e12, arXiv:1909.03562.

Let `syracuse n = oddPart (3n + 1)` (see `Collatz/Krasikov.lean`) and
`syrVal n = ν₂(3n + 1)`, so `3n + 1 = 2 ^ syrVal n * syracuse n`. The `k`-step valuation vector of
`n` is `syrVec k n = (syrVal n, syrVal (Syr n), …, syrVal (Syr^{k-1} n))`.
For `a : Fin k → ℕ` put `|a| = ∑ aᵢ` (`vsum a`) and
`off a = ∑_{i<k} 3^(k-1-i) 2^(a₀ + ⋯ + a_{i-1})` (`off a`), so `off a / 2^|a|` is Tao's
`F_k(a) = ∑_j 3^(k-j) 2^(-a_{[j,k]})` (Tao §6).

Main results:

* `affine` (Tao (1.5)/(1.7)): `2^|syrVec k n| * Syr^k n = 3^k n + off (syrVec k n)`.
* `uniqueness` (Tao Lemma 2.1): if all `aᵢ ≥ 1`, `m` is odd and `2^|a| m = 3^k n + off a`, then
  `a = syrVec k n` and `m = Syr^k n`.
* `off_div_injOn` (Tao Lemma 6.2): `a ↦ off a / 2^|a|` is injective on vectors with entries `≥ 1`.
* `card_syrVec_eq` / `prob_syrVec_eq` (exact special case of Tao Prop. 1.9): for `M ≥ |a| + 1`,
  exactly `2^(M - |a| - 1)` odd `n < 2^M` have `syrVec k n = a`; i.e. for `N` uniform on the odd
  residues mod `2^M`, `P(syrVec k N = a) = 2^(-|a|)`, the law of `k` i.i.d. `Geom(2)` variables.

Remarks on the statements.
* `affine` and `uniqueness` are stated for every `n : ℕ`, not only odd `n`: the identity
  `3n + 1 = 2^syrVal n * syracuse n` holds for all `n`, so the oddness hypothesis on `n` is not
  needed (the statements are thus slightly stronger than in the paper).
* `Syrac k : PMF (ZMod (3^k))` is Tao's `Syrac(ℤ/3^k)` (1.21), defined here as the law of
  `∑_{i<k} 3^(k-1-i) 2^(-(a_i + ⋯ + a_{k-1})) mod 3^k` for i.i.d. `a_i ~ Geom(2)` (built from
  Mathlib's `PMF.bind`/`PMF.map`). We prove the compatibility (1.22) (`Syrac_compat`) and the
  recursive description `Syrac_{k+1} = (3 Syrac_k + 1) 2^(-Geom(2))` (`Syrac_succ`; this is the
  recursion used in Tao's Lemma 1.12, stated here as an identity of laws).
* The proof of the counting statement does not go through parity vectors; it uses `affine` and
  `uniqueness` to show that `syrVec k n = a` is equivalent to the congruence
  `3^k n + off a ≡ 2^|a| (mod 2^(|a|+1))`, which singles out one residue class mod `2^(|a|+1)`.
-/

namespace Collatz.TaoSyracuse

open Collatz Finset

/-! ## Definitions -/

/-- The 2-adic valuation `ν₂(3n + 1)`. -/
def syrVal (n : ℕ) : ℕ := padicValNat 2 (3 * n + 1)

/-- The `k`-step valuation vector `(syrVal (Syr^i n))_{i<k}`. -/
def syrVec (k n : ℕ) : Fin k → ℕ := fun i => syrVal (syracuse^[i] n)

/-- `|a| = ∑ aᵢ`. -/
def vsum {k : ℕ} (a : Fin k → ℕ) : ℕ := ∑ i, a i

/-- The partial sum `a₀ + ⋯ + a_{i-1}`. -/
def psum {k : ℕ} (a : Fin k → ℕ) (i : ℕ) : ℕ := ∑ j ∈ univ.filter (fun j : Fin k => j.val < i), a j

/-- The offset `∑_{i<k} 3^(k-1-i) 2^(a₀ + ⋯ + a_{i-1})`. -/
def off {k : ℕ} (a : Fin k → ℕ) : ℕ := ∑ i : Fin k, 3 ^ (k - 1 - i) * 2 ^ psum a i

/-! ## Basic lemmas -/

lemma vsum_cons {k : ℕ} (v : ℕ) (a : Fin k → ℕ) :
    vsum (Fin.cons v a : Fin (k + 1) → ℕ) = v + vsum a := by
  simp [vsum, Fin.sum_univ_succ]

lemma psum_cons_zero {k : ℕ} (v : ℕ) (a : Fin k → ℕ) :
    psum (Fin.cons v a : Fin (k + 1) → ℕ) 0 = 0 := by
  simp [psum]

lemma psum_cons_succ {k : ℕ} (v : ℕ) (a : Fin k → ℕ) (i : ℕ) :
    psum (Fin.cons v a : Fin (k + 1) → ℕ) (i + 1) = v + psum a i := by
  simp [psum, Finset.sum_filter, Fin.sum_univ_succ]

lemma off_cons {k : ℕ} (v : ℕ) (a : Fin k → ℕ) :
    off (Fin.cons v a : Fin (k + 1) → ℕ) = 3 ^ k + 2 ^ v * off a := by
  simp only [off, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, psum_cons_succ, psum_cons_zero]
  rw [mul_sum]
  congr 1
  · simp
  · refine sum_congr rfl (fun i _ => ?_)
    rw [show k + 1 - 1 - (i.val + 1) = k - 1 - i.val by omega, pow_add]
    ring

lemma vsum_zero (a : Fin 0 → ℕ) : vsum a = 0 := by simp [vsum]

lemma off_zero (a : Fin 0 → ℕ) : off a = 0 := by simp [off]

lemma eq_cons {k : ℕ} (a : Fin (k + 1) → ℕ) : ∃ v a', a = (Fin.cons v a' : Fin (k + 1) → ℕ) :=
  ⟨a 0, Fin.tail a, (Fin.cons_self_tail a).symm⟩

lemma three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  rw [Nat.pow_mod]; simp

lemma off_odd {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 1 ≤ a i) : off a % 2 = 1 := by
  obtain ⟨v, a', rfl⟩ := eq_cons a
  have hv : 1 ≤ v := by simpa using ha 0
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  rw [off_cons, show 2 ^ (u + 1) * off a' = 2 * (2 ^ u * off a') by ring,
    Nat.add_mul_mod_self_left, three_pow_mod_two]

lemma one_le_vsum {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 1 ≤ a i) : 1 ≤ vsum a := by
  rw [vsum, Fin.sum_univ_succ]
  have := ha 0
  omega

lemma tail_ge {k : ℕ} {v : ℕ} {a : Fin k → ℕ} (ha : ∀ i, 1 ≤ (Fin.cons v a : Fin (k + 1) → ℕ) i) :
    ∀ i, 1 ≤ a i := fun i => by simpa using ha i.succ

/-- `3n + 1 = 2 ^ syrVal n * syracuse n`. -/
lemma syrVal_spec (n : ℕ) : 3 * n + 1 = 2 ^ syrVal n * syracuse n := by
  obtain ⟨v, hv, ho⟩ := exists_eq_pow_mul_oddPart (3 * n + 1) (by omega)
  have : syrVal n = v := by
    have h0 : oddPart (3 * n + 1) ≠ 0 := by omega
    rw [syrVal, Nat.padicValNat_def, hv, Nat.multiplicity_mul (by positivity) h0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd (by omega), add_zero]
  rw [this]
  exact hv

lemma syrVec_succ (k n : ℕ) :
    syrVec (k + 1) n = (Fin.cons (syrVal n) (syrVec k (syracuse n)) : Fin (k + 1) → ℕ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [syrVec]
  · simp [syrVec, Function.iterate_succ_apply]

lemma syracuse_iterate_odd {n : ℕ} (hn : n % 2 = 1) : ∀ k, syracuse^[k] n % 2 = 1
  | 0 => hn
  | k + 1 => by rw [Function.iterate_succ_apply']; exact syracuse_odd _

/-- If `2^x p = 2^y q` with `p, q` odd then `x = y` and `p = q`. -/
lemma two_pow_mul_odd_inj {x y p q : ℕ} (hp : p % 2 = 1) (hq : q % 2 = 1)
    (h : 2 ^ x * p = 2 ^ y * q) : x = y ∧ p = q := by
  have hpq : p = q := by rw [← oddPart_pow_mul hp x, h, oddPart_pow_mul hq y]
  subst hpq
  exact ⟨Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right (by omega) h), rfl⟩

/-! ## Tao (1.7): the affine formula -/

/-- **Tao (1.5)/(1.7).** `2^|syrVec k n| · Syr^k n = 3^k n + off (syrVec k n)`
(valid for every `n`, in particular for odd `n`). -/
theorem affine (k : ℕ) : ∀ n : ℕ,
    2 ^ vsum (syrVec k n) * syracuse^[k] n = 3 ^ k * n + off (syrVec k n) := by
  induction k with
  | zero => intro n; simp [vsum, off]
  | succ k ih =>
    intro n
    rw [syrVec_succ, vsum_cons, off_cons, Function.iterate_succ_apply, pow_add, mul_assoc, ih]
    have h := syrVal_spec n
    calc 2 ^ syrVal n * (3 ^ k * syracuse n + off (syrVec k (syracuse n)))
        = 3 ^ k * (2 ^ syrVal n * syracuse n) + 2 ^ syrVal n * off (syrVec k (syracuse n)) := by
          ring
      _ = _ := by rw [← h]; ring

/-! ## Tao Lemma 2.1: uniqueness -/

/-- **Tao Lemma 2.1.** If every `aᵢ ≥ 1`, `m` is odd and `2^|a| m = 3^k n + off a`, then
`a = syrVec k n` and `m = Syr^k n`. (The hypothesis that `n` is odd is not needed.) -/
theorem uniqueness : ∀ (k n : ℕ) (a : Fin k → ℕ) (m : ℕ), (∀ i, 1 ≤ a i) → m % 2 = 1 →
    2 ^ vsum a * m = 3 ^ k * n + off a → a = syrVec k n ∧ m = syracuse^[k] n
  | 0, n, a, m, _, _, h => by
    refine ⟨Subsingleton.elim _ _, ?_⟩
    simpa [vsum, off] using h
  | k + 1, n, a, m, ha, hm, h => by
    obtain ⟨v, a', rfl⟩ := eq_cons a
    have ha' := tail_ge ha
    rw [vsum_cons, off_cons] at h
    have hs := syrVal_spec n
    have hy : syracuse n % 2 = 1 := syracuse_odd n
    have h2 : 2 ^ (v + vsum a') * m =
        3 ^ k * (2 ^ syrVal n * syracuse n) + 2 ^ v * off a' := by rw [h, ← hs]; ring
    have hvw : v = syrVal n ∧ 2 ^ vsum a' * m = 3 ^ k * syracuse n + off a' := by
      cases k with
      | zero =>
        rw [vsum_zero, off_zero] at h2 ⊢
        simp only [add_zero, pow_zero, one_mul] at h2 ⊢
        exact two_pow_mul_odd_inj hm hy h2
      | succ k =>
        have hc := off_odd a' ha'
        have h3 := three_pow_mod_two (k + 1)
        obtain ⟨s, hs'⟩ : ∃ s, vsum a' = s + 1 := ⟨vsum a' - 1, by have := one_le_vsum a' ha'; omega⟩
        rw [hs'] at h2 ⊢
        have h3y : 3 ^ (k + 1) * syracuse n % 2 = 1 := by rw [Nat.mul_mod, h3, hy]
        rcases lt_trichotomy v (syrVal n) with hlt | heq | hgt
        · exfalso
          obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hlt
          rw [he] at h2
          have h4 : 2 ^ v * (2 * (2 ^ s * m)) =
              2 ^ v * (2 * (3 ^ (k + 1) * 2 ^ e * syracuse n) + off a') := by
            rw [show 2 ^ v * (2 * (2 ^ s * m)) = 2 ^ (v + (s + 1)) * m by ring, h2]; ring
          have h5 := Nat.eq_of_mul_eq_mul_left (by positivity) h4
          omega
        · refine ⟨heq, ?_⟩
          rw [← heq] at h2
          have h4 : 2 ^ v * (2 ^ (s + 1) * m) = 2 ^ v * (3 ^ (k + 1) * syracuse n + off a') := by
            rw [← mul_assoc, ← pow_add, h2]; ring
          exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
        · exfalso
          obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hgt
          rw [he] at h2
          have h4 : 2 ^ syrVal n * (2 * (2 ^ (e + s + 1) * m)) =
              2 ^ syrVal n * (3 ^ (k + 1) * syracuse n + 2 * (2 ^ e * off a')) := by
            rw [← mul_assoc, show 2 ^ syrVal n * 2 = 2 ^ (syrVal n + 1) by ring]
            calc 2 ^ (syrVal n + 1) * (2 ^ (e + s + 1) * m)
                = 2 ^ (syrVal n + e + 1 + (s + 1)) * m := by ring
              _ = _ := by rw [h2]; ring
          have h5 := Nat.eq_of_mul_eq_mul_left (by positivity) h4
          omega
    obtain ⟨rfl, h3⟩ := hvw
    obtain ⟨e1, e2⟩ := uniqueness k (syracuse n) a' m ha' hm h3
    refine ⟨?_, ?_⟩
    · rw [syrVec_succ, e1]
    · rw [Function.iterate_succ_apply, e2]

/-! ## Tao Lemma 6.2: injectivity of the offsets -/

/-- Vectors with entries `≥ 1` are determined by `|a|` and `off a`. -/
theorem off_inj : ∀ (k : ℕ) (a b : Fin k → ℕ), (∀ i, 1 ≤ a i) → (∀ i, 1 ≤ b i) →
    vsum a = vsum b → off a = off b → a = b
  | 0, _, _, _, _, _, _ => Subsingleton.elim _ _
  | k + 1, a, b, ha, hb, hs, ho => by
    obtain ⟨v, a', rfl⟩ := eq_cons a
    obtain ⟨u, b', rfl⟩ := eq_cons b
    have ha' := tail_ge ha
    have hb' := tail_ge hb
    rw [off_cons, off_cons] at ho
    rw [vsum_cons, vsum_cons] at hs
    have ho' : 2 ^ v * off a' = 2 ^ u * off b' := by omega
    have key : v = u ∧ off a' = off b' := by
      cases k with
      | zero =>
        rw [vsum_zero, vsum_zero] at hs
        exact ⟨by omega, by rw [off_zero, off_zero]⟩
      | succ k => exact two_pow_mul_odd_inj (off_odd a' ha') (off_odd b' hb') ho'
    obtain ⟨rfl, h2⟩ := key
    rw [off_inj k a' b' ha' hb' (by omega) h2]

/-- **Tao Lemma 6.2.** The map `a ↦ off a / 2^|a|` (Tao's `F_k`) is
injective on the vectors `a : Fin k → ℕ` with all entries `≥ 1`. -/
theorem off_div_injOn (k : ℕ) :
    Set.InjOn (fun a : Fin k → ℕ => (off a : ℚ) / 2 ^ vsum a) {a | ∀ i, 1 ≤ a i} := by
  intro a ha b hb h
  cases k with
  | zero => exact Subsingleton.elim _ _
  | succ k =>
    simp only at h
    have h' : 2 ^ vsum b * off a = 2 ^ vsum a * off b := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h
      have : ((off a * 2 ^ vsum b : ℕ) : ℚ) = ((off b * 2 ^ vsum a : ℕ) : ℚ) := by
        push_cast; exact h
      have := Nat.cast_injective this
      linarith
    obtain ⟨e1, e2⟩ := two_pow_mul_odd_inj (off_odd a ha) (off_odd b hb) h'
    exact off_inj _ a b ha hb e1.symm e2

/-! ## The exact special case of Tao Prop. 1.9 -/

/-- Each residue class `r < q` meets `[0, q t)` in exactly `t` points. -/
lemma card_filter_mod_eq (q t r : ℕ) (hr : r < q) :
    ((range (q * t)).filter (fun n => n % q = r)).card = t := by
  have hq : 0 < q := by omega
  have e : (range (q * t)).filter (fun n => n % q = r) =
      (range t).map ⟨fun i => q * i + r, fun i j (h : q * i + r = q * j + r) =>
        Nat.eq_of_mul_eq_mul_left hq (by omega)⟩ := by
    ext n
    simp only [mem_filter, mem_range, mem_map]
    change n < q * t ∧ n % q = r ↔ ∃ a, a < t ∧ q * a + r = n
    constructor
    · rintro ⟨hn, rfl⟩
      exact ⟨n / q, Nat.div_lt_of_lt_mul hn, Nat.div_add_mod n q⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, ?_⟩
      · have : q * (i + 1) ≤ q * t := Nat.mul_le_mul_left _ hi
        rw [mul_add, mul_one] at this
        omega
      · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [e, card_map, card_range]

/-- `syrVec k n = a` (for odd `n`) is the congruence `3^k n + off a ≡ 2^|a| (mod 2^(|a|+1))`. -/
lemma syrVec_eq_iff {k : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    (n % 2 = 1 ∧ syrVec k n = a) ↔ (3 ^ k * n + off a) % 2 ^ (vsum a + 1) = 2 ^ vsum a := by
  have hlt : 2 ^ vsum a < 2 ^ (vsum a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  constructor
  · rintro ⟨hn, rfl⟩
    rw [← affine]
    have hm := syracuse_iterate_odd hn k
    have e : 2 ^ vsum (syrVec k n) * syracuse^[k] n =
        2 ^ (vsum (syrVec k n) + 1) * (syracuse^[k] n / 2) + 2 ^ vsum (syrVec k n) := by
      conv_lhs => rw [← Nat.div_add_mod (syracuse^[k] n) 2, hm]
      ring
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  · intro h
    set x := 3 ^ k * n + off a with hx
    have e : 2 ^ vsum a * (2 * (x / 2 ^ (vsum a + 1)) + 1) = x := by
      conv_rhs => rw [← Nat.div_add_mod x (2 ^ (vsum a + 1)), h]
      ring
    obtain ⟨e1, -⟩ := uniqueness k n a _ ha (by omega) (e.trans hx)
    refine ⟨?_, e1.symm⟩
    cases k with
    | zero =>
      rw [hx, off_zero, vsum_zero] at h
      simpa using h
    | succ k =>
      have hc := off_odd a ha
      obtain ⟨s, hs⟩ : ∃ s, vsum a = s + 1 := ⟨vsum a - 1, by have := one_le_vsum a ha; omega⟩
      rw [hs, pow_succ] at e
      have h3 : 3 ^ (k + 1) * n % 2 = n % 2 := by
        rw [Nat.mul_mod, three_pow_mod_two, one_mul, Nat.mod_mod]
      have e' : 2 * (2 ^ s * (2 * (x / 2 ^ (s + 1 + 1)) + 1)) = 3 ^ (k + 1) * n + off a := by
        rw [hx] at e; rw [← e]; ring
      omega

/-- The congruence `3^k n + off a ≡ 2^|a| (mod 2^(|a|+1))` defines a single residue class. -/
lemma exists_residue {k : ℕ} (a : Fin k → ℕ) :
    ∃ c < 2 ^ (vsum a + 1), ∀ n,
      (3 ^ k * n + off a) % 2 ^ (vsum a + 1) = 2 ^ vsum a ↔ n % 2 ^ (vsum a + 1) = c := by
  set q := 2 ^ (vsum a + 1) with hq
  have : NeZero q := ⟨by positivity⟩
  have hcop : Nat.Coprime 3 q := Nat.Coprime.pow_right _ (by norm_num)
  set u : (ZMod q)ˣ := (ZMod.unitOfCoprime 3 hcop) ^ k with hu_def
  have hu : (u : ZMod q) = 3 ^ k := by simp [u]
  set x : ZMod q := u⁻¹ * ((2 ^ vsum a : ℕ) - (off a : ℕ)) with hx
  refine ⟨x.val, ZMod.val_lt x, fun n => ?_⟩
  have hlt : 2 ^ vsum a < q := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [← Nat.mod_eq_of_lt hlt, ← Nat.mod_eq_of_lt (ZMod.val_lt x),
    ← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val,
    ZMod.cast_id', id, hx, Units.eq_inv_mul_iff_mul_eq, eq_sub_iff_add_eq, hu]
  push_cast
  rfl

/-- **Exact special case of Tao Prop. 1.9.** If all `aᵢ ≥ 1` and `M ≥ |a| + 1`, exactly
`2^(M - |a| - 1)` odd `n < 2^M` have valuation vector `syrVec k n = a`. -/
theorem card_syrVec_eq {k : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i) (M : ℕ) (hM : vsum a + 1 ≤ M) :
    ((range (2 ^ M)).filter (fun n => n % 2 = 1 ∧ syrVec k n = a)).card = 2 ^ (M - vsum a - 1) := by
  obtain ⟨c, hc, hcn⟩ := exists_residue a
  have key : ∀ n, (n % 2 = 1 ∧ syrVec k n = a) ↔ n % 2 ^ (vsum a + 1) = c := fun n => by
    rw [← hcn]; exact syrVec_eq_iff a ha n
  rw [filter_congr (fun n _ => key n),
    show 2 ^ M = 2 ^ (vsum a + 1) * 2 ^ (M - vsum a - 1) by rw [← pow_add]; congr 1; omega]
  exact card_filter_mod_eq _ _ _ hc

/-- The number of odd `n < 2^M` is `2^(M-1)` (for `M ≥ 1`). -/
lemma card_odd (M : ℕ) (hM : 1 ≤ M) :
    ((range (2 ^ M)).filter (fun n => n % 2 = 1)).card = 2 ^ (M - 1) := by
  rw [show 2 ^ M = 2 * 2 ^ (M - 1) by rw [← pow_succ']; congr 1; omega]
  exact card_filter_mod_eq _ _ _ (by norm_num)

/-- **Tao Prop. 1.9, exact form.** For `N` uniform on the odd residues mod `2^M` with
`M ≥ |a| + 1`, `P(syrVec k N = a) = 2^(-|a|)`: the valuation vector is distributed exactly as `k`
independent `Geom(2)` variables (`P(aᵢ = j) = 2^(-j)`, `j ≥ 1`). -/
theorem prob_syrVec_eq {k : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i) (M : ℕ) (hM : vsum a + 1 ≤ M) :
    (((range (2 ^ M)).filter (fun n => n % 2 = 1 ∧ syrVec k n = a)).card : ℚ) /
      ((range (2 ^ M)).filter (fun n => n % 2 = 1)).card = 1 / 2 ^ vsum a := by
  rw [card_syrVec_eq a ha M hM, card_odd M (by omega)]
  rw [show M - 1 = (M - vsum a - 1) + vsum a by omega, pow_add]
  push_cast
  field_simp

/-! ## The Syracuse random variables `Syrac(ℤ/3^k)` (Tao (1.21), (1.22), Lemma 1.12) -/

section Syrac

open scoped ENNReal

/-- The mass function of `Geom(2)` on `ℕ`: `a ↦ 2^(-a)` for `a ≥ 1`, and `0 ↦ 0`. -/
noncomputable def geomFun (a : ℕ) : ℝ≥0∞ := if a = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ a

lemma geomFun_hasSum : HasSum geomFun 1 := by
  have h1 : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 1 := by
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have h2 : HasSum (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1)) 1 := by
    rw [← h1]; exact CompleteLattice.summable.hasSum
  have e : (geomFun ∘ Nat.succ) = fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    funext n; simp [geomFun]
  rw [← Function.Injective.hasSum_iff Nat.succ_injective, e]
  · exact h2
  · intro x hx
    have : x = 0 := by
      by_contra h
      exact hx ⟨x - 1, by simp; omega⟩
    simp [geomFun, this]

/-- The geometric law `Geom(2)` on `ℕ`: `P(a) = 2^(-a)` for `a ≥ 1`, `P(0) = 0`. -/
noncomputable def geom : PMF ℕ := ⟨geomFun, geomFun_hasSum⟩

lemma geom_apply (a : ℕ) : geom a = if a = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ a := rfl

/-- `k` independent copies of `Geom(2)`, as a law on `Fin k → ℕ`. -/
noncomputable def geomVec : (k : ℕ) → PMF (Fin k → ℕ)
  | 0 => PMF.pure Fin.elim0
  | k + 1 => geom.bind (fun v => (geomVec k).map (Fin.cons v))

lemma geomVec_succ (k : ℕ) : geomVec (k + 1) = geom.bind (fun v => (geomVec k).map (Fin.cons v)) :=
  rfl

/-- Appending instead of prepending the new coordinate gives the same law. -/
lemma geomVec_succ_snoc : ∀ k : ℕ,
    geomVec (k + 1) = (geomVec k).bind (fun a => geom.map (Fin.snoc a))
  | 0 => by
    simp only [geomVec, PMF.pure_map, PMF.pure_bind]
    rw [← PMF.bind_pure_comp]
    congr 1
    funext v
    simp only [Function.comp_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => j.elim0) i
    rfl
  | k + 1 => by
    have e1 : geomVec (k + 2) = geom.bind (fun v =>
        ((geomVec k).bind (fun a => geom.map (Fin.snoc a))).map (Fin.cons v)) := by
      rw [geomVec_succ (k + 1), geomVec_succ_snoc k]
    rw [e1, geomVec_succ k, PMF.bind_bind]
    congr 1
    funext v
    rw [PMF.map_bind, PMF.bind_map]
    congr 1
    funext a
    rw [Function.comp_apply, PMF.map_comp]
    congr 1
    funext w
    exact Fin.cons_snoc_eq_snoc_cons v a w

/-- Tao's sum `∑_{i<k} 3^(k-1-i) 2^(-(a_i + ⋯ + a_{k-1}))`, computed in `ZMod N`. -/
noncomputable def syrSum (N : ℕ) {k : ℕ} (a : Fin k → ℕ) : ZMod N :=
  ∑ i : Fin k, 3 ^ (k - 1 - i) * (2⁻¹ : ZMod N) ^ (vsum a - psum a i)

/-- **Tao (1.21).** `Syrac(ℤ/3^k)`: the law of `∑_{i<k} 3^(k-1-i) 2^(-(a_i + ⋯ + a_{k-1}))`
mod `3^k` for independent `a_i ~ Geom(2)`. Tao writes the sum with prefix sums
`∑_m 3^(m-1) 2^(-a_{[1,m]})`; reversing the i.i.d. vector `a` turns one form into the other, so the
two laws coincide. -/
noncomputable def Syrac (k : ℕ) : PMF (ZMod (3 ^ k)) := (geomVec k).map (syrSum (3 ^ k))

lemma two_mul_inv_two {N : ℕ} (h : Nat.Coprime 2 N) : (2 : ZMod N) * 2⁻¹ = 1 := by
  simpa using ZMod.coe_mul_inv_eq_one 2 h

lemma ringHom_inv_two {n m : ℕ} (hn : Nat.Coprime 2 n) (hm : Nat.Coprime 2 m)
    (f : ZMod n →+* ZMod m) : f 2⁻¹ = 2⁻¹ := by
  calc f 2⁻¹ = f 2⁻¹ * (2 * 2⁻¹) := by rw [two_mul_inv_two hm, mul_one]
    _ = f (2⁻¹ * 2) * 2⁻¹ := by rw [map_mul, map_ofNat]; ring
    _ = 2⁻¹ := by rw [mul_comm (2⁻¹ : ZMod n), two_mul_inv_two hn, map_one, one_mul]

lemma coprime_two_three_pow (k : ℕ) : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)

lemma map_syrSum {n m : ℕ} (hn : Nat.Coprime 2 n) (hm : Nat.Coprime 2 m) (f : ZMod n →+* ZMod m)
    {k : ℕ} (a : Fin k → ℕ) : f (syrSum n a) = syrSum m a := by
  simp only [syrSum, map_sum, map_mul, map_pow, map_ofNat, ringHom_inv_two hn hm f]

lemma syrSum_cons (N : ℕ) {k : ℕ} (v : ℕ) (a : Fin k → ℕ) :
    syrSum N (Fin.cons v a : Fin (k + 1) → ℕ) = 3 ^ k * (2⁻¹ : ZMod N) ^ (v + vsum a) + syrSum N a := by
  simp only [syrSum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, psum_cons_succ, psum_cons_zero,
    vsum_cons]
  congr 1
  refine sum_congr rfl (fun i _ => ?_)
  rw [Nat.add_sub_add_left, show k + 1 - 1 - (i.val + 1) = k - 1 - i.val by omega]

lemma vsum_snoc {k : ℕ} (a : Fin k → ℕ) (v : ℕ) :
    vsum (Fin.snoc a v : Fin (k + 1) → ℕ) = vsum a + v := by
  simp [vsum, Fin.sum_univ_castSucc]

lemma psum_snoc {k : ℕ} (a : Fin k → ℕ) (v : ℕ) {i : ℕ} (hi : i ≤ k) :
    psum (Fin.snoc a v : Fin (k + 1) → ℕ) i = psum a i := by
  have : ¬ k < i := by omega
  simp [psum, Finset.sum_filter, Fin.sum_univ_castSucc, this]

lemma psum_le_vsum {k : ℕ} (a : Fin k → ℕ) (i : ℕ) : psum a i ≤ vsum a :=
  Finset.sum_le_sum_of_subset (filter_subset _ _)

lemma psum_eq_vsum {k : ℕ} (a : Fin k → ℕ) : psum a k = vsum a := by
  simp only [psum, vsum]
  congr 1
  ext j
  simp

lemma syrSum_snoc (N : ℕ) {k : ℕ} (a : Fin k → ℕ) (v : ℕ) :
    syrSum N (Fin.snoc a v : Fin (k + 1) → ℕ) = (3 * syrSum N a + 1) * (2⁻¹ : ZMod N) ^ v := by
  simp only [syrSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, vsum_snoc,
    psum_snoc a v (le_of_lt (Fin.isLt _)), psum_snoc a v le_rfl, psum_eq_vsum]
  rw [add_mul, mul_sum, sum_mul]
  congr 1
  · refine sum_congr rfl (fun i _ => ?_)
    rw [show vsum a + v - psum a i = (vsum a - psum a i) + v by
      have := psum_le_vsum a i; omega, pow_add,
      show k + 1 - 1 - i.val = (k - 1 - i.val) + 1 by have := i.isLt; omega, pow_succ]
    ring
  · simp

/-- Multiplication by `3` on `ZMod (3^(k+1))` only sees the residue mod `3^k`. -/
lemma three_mul_val_cast (k : ℕ) (y : ZMod (3 ^ (k + 1))) :
    3 * (((ZMod.castHom (pow_dvd_pow 3 (Nat.le_succ k)) (ZMod (3 ^ k)) y).val : ℕ) :
      ZMod (3 ^ (k + 1))) = 3 * y := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val y]
  have e : ((3 * (y.val % 3 ^ k) : ℕ) : ZMod (3 ^ (k + 1))) = ((3 * y.val : ℕ) : ZMod (3 ^ (k + 1))) := by
    rw [ZMod.natCast_eq_natCast_iff']
    generalize y.val = w
    rw [pow_succ', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
  exact_mod_cast e

/-- **Tao (1.22).** Compatibility: `Syrac(ℤ/3^(k+1)) mod 3^k = Syrac(ℤ/3^k)`. -/
theorem Syrac_compat (k : ℕ) :
    (Syrac (k + 1)).map (ZMod.castHom (pow_dvd_pow 3 (Nat.le_succ k)) (ZMod (3 ^ k))) = Syrac k := by
  rw [Syrac, PMF.map_comp, geomVec, PMF.map_bind]
  have h : ∀ v, (ZMod.castHom (pow_dvd_pow 3 (Nat.le_succ k)) (ZMod (3 ^ k)) ∘ syrSum (3 ^ (k + 1)))
      ∘ (fun a => (Fin.cons v a : Fin (k + 1) → ℕ)) = syrSum (3 ^ k) := by
    intro v
    funext a
    simp only [Function.comp_apply]
    rw [map_syrSum (coprime_two_three_pow _) (coprime_two_three_pow _), syrSum_cons]
    have h3 : ((3 ^ k : ℕ) : ZMod (3 ^ k)) = 0 := ZMod.natCast_self _
    push_cast at h3
    rw [h3, zero_mul, zero_add]
  simp only [PMF.map_comp, h, PMF.bind_const]
  rfl

/-- **Recursion (Tao Lemma 1.12 / the recursive description of `Syrac`).**
`Syrac(ℤ/3^(k+1)) = (3 Syrac(ℤ/3^k) + 1) 2^(-a)` with `a ~ Geom(2)` independent of `Syrac(ℤ/3^k)`;
here `3x` for `x ∈ ℤ/3^k` is the well-defined element of `ℤ/3^(k+1)` obtained from any lift. -/
theorem Syrac_succ (k : ℕ) :
    Syrac (k + 1) = (Syrac k).bind (fun x =>
      geom.map (fun v => (3 * ((x.val : ℕ) : ZMod (3 ^ (k + 1))) + 1) * (2⁻¹ : ZMod _) ^ v)) := by
  rw [Syrac, geomVec_succ_snoc, PMF.map_bind, Syrac, PMF.bind_map]
  congr 1
  funext a
  rw [PMF.map_comp, Function.comp_apply]
  congr 1
  funext v
  rw [Function.comp_apply, syrSum_snoc]
  congr 2
  rw [← map_syrSum (coprime_two_three_pow (k + 1)) (coprime_two_three_pow k)
    (ZMod.castHom (pow_dvd_pow 3 (Nat.le_succ k)) (ZMod (3 ^ k))), three_mul_val_cast]

end Syrac

end Collatz.TaoSyracuse

/-! ## Axiom audit -/

/-- info: 'Collatz.TaoSyracuse.affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TaoSyracuse.affine

/--
info: 'Collatz.TaoSyracuse.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.uniqueness

/--
info: 'Collatz.TaoSyracuse.off_div_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.off_div_injOn

/--
info: 'Collatz.TaoSyracuse.card_syrVec_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.card_syrVec_eq

/--
info: 'Collatz.TaoSyracuse.prob_syrVec_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.prob_syrVec_eq

/--
info: 'Collatz.TaoSyracuse.Syrac_compat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.Syrac_compat

/--
info: 'Collatz.TaoSyracuse.Syrac_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Collatz.TaoSyracuse.Syrac_succ
