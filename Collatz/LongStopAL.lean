import Collatz.LongStop
import Collatz.LSA.Basic

/-!
# Long stopping times from an Applegate–Lagarias tree search (soundness)

`Collatz.LSA` re-runs the Applegate–Lagarias search for a ternary prefix code of residue classes
of `3`-adic units in the kernel. This file proves it sound:

* `chunk_sound`: `chunk P Q F r0 js Ts = true` (for `r0 ∈ {1, 2}` and digits `js` below `3`)
  gives `Covered P Q r M` for the class `(r, M) = cls r0 3 js`: every `a ≡ r (mod M)` is the end
  `T^k n = a` of a path of length `k ≥ 1` from a unit `n` with at least `P k / Q` odd steps.
* `covered_split`: the three children of a class cover it (to assemble chunks).
* `long_stopping_AL`: if every unit is covered, then for every `N` some `n` has total stopping
  time exactly `L + 2 ≥ N` and `Q log n - 2P log 3 ≤ (Q log 2 - P log 3) σ(n)`; i.e. infinitely
  many `n` need `σ(n) ≥ γ log n - c` steps with `γ = Q / (Q log 2 - P log 3)`.

Hints (the bands `Ts`, the fuel `F`) only steer the search: any values give a sound check.
-/

namespace Collatz.LSA

open Collatz

/-! ## Odd counts along concatenated paths -/

lemma oddCount_succ' : ∀ j r, oddCount (j + 1) r = r % 2 + oddCount j (kstepT r)
  | 0, r => by simp [oddCount]
  | j + 1, r => by
    rw [oddCount_succ, oddCount_succ' j r, oddCount_succ, Function.iterate_succ_apply]
    omega

lemma oddCount_add (a n : ℕ) : ∀ b, oddCount (a + b) n = oddCount a n + oddCount b (kstepT^[a] n)
  | 0 => by simp [oddCount]
  | b + 1 => by
    rw [← Nat.add_assoc, oddCount_succ, oddCount_add a n b, oddCount_succ,
      ← Function.iterate_add_apply, Nat.add_comm b a]
    omega

/-! ## The invariants -/

/-- Every `a ≡ r (mod M)` ends a path of ratio `≥ P/Q` starting at a unit. -/
def Covered (P Q r M : ℕ) : Prop :=
  ∀ a, a % M = r → ∃ n k, 0 < k ∧ kstepT^[k] n = a ∧ n % 3 ≠ 0 ∧ P * k ≤ Q * oddCount k n

/-- The nodes `x + s t` reach `r + M t` along paths of length `k` with `w` odd steps. -/
def Good (r M x s k w : ℕ) : Prop :=
  ∀ t, kstepT^[k] (x + s * t) = r + M * t ∧ oddCount k (x + s * t) = w

/-- A frontier entry `(x, p, d)` of the class `(r, M)`: a node `x` with step `3p`, deficit
`d = P k - Q w`. -/
def EntOK (P Q r M : ℕ) (e : Ent) : Prop :=
  ∃ k w, e.2.2 + Q * w = P * k ∧ Good r M e.1 (3 * e.2.1) k w

def AllOK (P Q r M : ℕ) (l : List Ent) : Prop := ∀ e ∈ l, EntOK P Q r M e

/-- The meaning of a search result: `none` = closed (covered), `some l` = valid entries. -/
def ResOK (P Q r M : ℕ) : Option (List Ent) → Prop
  | none => Covered P Q r M
  | some l => AllOK P Q r M l

lemma good_even {r M x s k w : ℕ} (h : Good r M x s k w) : Good r M (2 * x) (2 * s) (k + 1) w := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  have e : 2 * x + 2 * s * t = 2 * (x + s * t) := by ring
  have hT : kstepT (2 * (x + s * t)) = x + s * t := by rw [kstepT_of_even (by omega)]; omega
  rw [e, Function.iterate_succ_apply, hT, oddCount_succ', hT]
  exact ⟨h1, by omega⟩

lemma good_pow {r M x s k w : ℕ} (h : Good r M x s k w) :
    ∀ g, Good r M (x * 2 ^ g) (s * 2 ^ g) (k + g) w
  | 0 => by simpa using h
  | g + 1 => by
    have := good_even (good_pow h g)
    rw [show x * 2 ^ (g + 1) = 2 * (x * 2 ^ g) by ring, show s * 2 ^ (g + 1) = 2 * (s * 2 ^ g) by ring,
      show k + (g + 1) = k + g + 1 by ring]
    exact this

lemma good_odd {r M x u k w : ℕ} (h : Good r M x (9 * u) k w) (hx : x % 9 = 2 ∨ x % 9 = 8) :
    Good r M ((2 * x - 1) / 3) (3 * (2 * u)) (k + 1) (w + 1) ∧
      ∀ t, ((2 * x - 1) / 3 + 3 * (2 * u) * t) % 3 ≠ 0 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · obtain ⟨h1, h2⟩ := h t
    have e1 : 3 * (2 * u) * t = 6 * (u * t) := by ring
    have e2 : 9 * u * t = 9 * (u * t) := by ring
    rw [e2] at h1 h2
    rw [e1]
    generalize u * t = v at h1 h2 ⊢
    have hodd : ((2 * x - 1) / 3 + 6 * v) % 2 = 1 := by omega
    have hT : kstepT ((2 * x - 1) / 3 + 6 * v) = x + 9 * v := by rw [kstepT_of_odd hodd]; omega
    rw [Function.iterate_succ_apply, hT, oddCount_succ', hT, hodd]
    exact ⟨h1, by omega⟩
  · have e1 : 3 * (2 * u) * t = 6 * (u * t) := by ring
    rw [e1]
    omega

lemma oddOk_spec {y : ℕ} (h : oddOk y = true) : y % 9 = 2 ∨ y % 9 = 8 := by
  unfold oddOk at h
  simp only [Bool.or_eq_true, Nat.beq_eq] at h
  exact h

/-! ## Soundness of `chain`, `node`, `ext` -/

lemma chain_sound (P Q T r M : ℕ) : ∀ fuel y p d acc, AllOK P Q r M acc →
    (∃ k w, d + Q * w = P * k ∧ Good r M y (9 * p) k w) → ResOK P Q r M (chain P Q T fuel y p d acc)
  | 0, _, _, _, acc, hacc, _ => hacc
  | fuel + 1, y, p, d, acc, hacc, ⟨k, w, hd, hg⟩ => by
    have e : chain P Q T (fuel + 1) y p d acc =
      (bif oddOk y then
        (bif Nat.ble (d + P) Q then none
         else bif Nat.ble (d + P) (Q + T) then
           chain P Q T fuel (y <<< (bif Nat.beq (y % 9) 2 then 2 else 4))
             (p <<< (bif Nat.beq (y % 9) 2 then 2 else 4))
             (d + (bif Nat.beq (y % 9) 2 then 2 else 4) * P)
             (((2 * y - 1) / 3, 2 * p, d + P - Q) :: acc)
         else some acc)
      else some acc) := rfl
    rw [e]
    generalize hgg : (bif Nat.beq (y % 9) 2 then 2 else 4) = g
    cases hy : oddOk y
    · exact hacc
    have hy9 := oddOk_spec hy
    have ho := good_odd hg hy9
    simp only [Bool.cond_true]
    cases hc : Nat.ble (d + P) Q
    · simp only [Bool.cond_false]
      have hc' : ¬ d + P ≤ Q := fun h' => by rw [Nat.ble_eq_true_of_le h'] at hc; exact absurd hc (by simp)
      -- the new entry
      have hnew : EntOK P Q r M ((2 * y - 1) / 3, 2 * p, d + P - Q) := by
        refine ⟨k + 1, w + 1, ?_, ho.1⟩
        show d + P - Q + Q * (w + 1) = P * (k + 1)
        rw [Nat.mul_add, Nat.mul_add]; omega
      have hacc' : AllOK P Q r M (((2 * y - 1) / 3, 2 * p, d + P - Q) :: acc) := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hnew
        · exact hacc e he
      cases Nat.ble (d + P) (Q + T)
      · exact hacc
      · simp only [Bool.cond_true]
        apply chain_sound P Q T r M fuel _ _ _ _ hacc'
        refine ⟨k + g, w, ?_, ?_⟩
        · rw [Nat.mul_add]; rw [Nat.mul_comm P g] at *; omega
        · rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show 9 * (p * 2 ^ g) = 9 * p * 2 ^ g by ring]
          exact good_pow hg g
    · simp only [Bool.cond_true]
      have hc' : d + P ≤ Q := Nat.le_of_ble_eq_true hc
      intro a ha
      refine ⟨(2 * y - 1) / 3 + 3 * (2 * p) * (a / M), k + 1, by omega, ?_, ho.2 _, ?_⟩
      · rw [(ho.1 (a / M)).1, ← ha, Nat.mod_add_div]
      · rw [(ho.1 (a / M)).2, Nat.mul_add, Nat.mul_add]; omega

lemma node_sound (P Q T F r M x p d : ℕ) (acc : List Ent) (hacc : AllOK P Q r M acc)
    (h : ∃ k w, d + Q * w = P * k ∧ Good r M x (9 * p) k w) :
    ResOK P Q r M (node P Q T F x p d acc) := by
  obtain ⟨k, w, hd, hg⟩ := h
  unfold node
  generalize i0 (Nat.mod x 9) = i
  apply chain_sound _ _ _ _ _ _ _ _ _ _ hacc
  refine ⟨k + i, w, ?_, ?_⟩
  · show d + i * P + Q * w = P * (k + i)
    rw [Nat.mul_add, Nat.mul_comm i P]; omega
  · show Good r M (x <<< i) (9 * (p <<< i)) (k + i) w
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show 9 * (p * 2 ^ i) = 9 * p * 2 ^ i by ring]
    exact good_pow hg i

lemma lift_ok {P Q r M j : ℕ} {e : Ent} (h : EntOK P Q r M e) :
    ∃ k w, e.2.2 + Q * w = P * k ∧ Good (r + j * M) (3 * M) (e.1 + 3 * j * e.2.1) (9 * e.2.1) k w := by
  obtain ⟨k, w, hd, hg⟩ := h
  refine ⟨k, w, hd, fun t => ?_⟩
  have := hg (j + 3 * t)
  rw [show e.1 + 3 * e.2.1 * (j + 3 * t) = e.1 + 3 * j * e.2.1 + 9 * e.2.1 * t by ring,
    show r + M * (j + 3 * t) = r + j * M + 3 * M * t by ring] at this
  exact this

lemma ext_sound (P Q T F j r M : ℕ) (f : List Ent) (hf : AllOK P Q r M f) :
    ResOK P Q (r + j * M) (3 * M) (ext P Q T F j f) := by
  unfold ext
  suffices H : ∀ (f : List Ent) (acc : List Ent), AllOK P Q r M f → AllOK P Q (r + j * M) (3 * M) acc →
      ResOK P Q (r + j * M) (3 * M)
        (List.rec (motive := fun _ => List Ent → Option (List Ent)) (fun acc => some acc)
          (fun e _ ih acc =>
            bindO (node P Q T F (Nat.add e.1 (Nat.mul (Nat.mul 3 j) e.2.1)) e.2.1 e.2.2 acc) ih) f acc)
    from H f [] hf (by intro e he; simp at he)
  intro f
  induction f with
  | nil => intro acc _ hacc; exact hacc
  | cons e f ih =>
    intro acc hf hacc
    have hn := node_sound P Q T F (r + j * M) (3 * M) (e.1 + 3 * j * e.2.1) e.2.1 e.2.2 acc hacc
      (lift_ok (hf e (List.mem_cons_self ..)))
    show ResOK P Q (r + j * M) (3 * M) (bindO (node P Q T F (e.1 + 3 * j * e.2.1) e.2.1 e.2.2 acc) _)
    revert hn
    cases node P Q T F (e.1 + 3 * j * e.2.1) e.2.1 e.2.2 acc with
    | none => intro hn; exact hn
    | some acc' => intro hn; exact ih acc' (fun e' he' => hf e' (List.mem_cons_of_mem _ he')) hn

/-! ## Soundness of `cover`, `desc`, `chunk` -/

/-- The three children of a class cover it. -/
lemma covered_split {P Q r M : ℕ} (h0 : Covered P Q r (3 * M)) (h1 : Covered P Q (r + M) (3 * M))
    (h2 : Covered P Q (r + 2 * M) (3 * M)) : Covered P Q r M := by
  intro a ha
  have hm : a % (3 * M) = a % M + M * (a / M % 3) := by
    rw [Nat.mul_comm 3 M]; exact Nat.mod_mul
  rw [ha] at hm
  have : a / M % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hj : a / M % 3
  · exact h0 a (by omega)
  · exact h1 a (by omega)
  · exact h2 a (by omega)

lemma covered_of_res {P Q T F j r M : ℕ} {f : List Ent} {C : List Ent → Bool}
    (hf : AllOK P Q r M f)
    (ih : ∀ g, AllOK P Q (r + j * M) (3 * M) g → C g = true → Covered P Q (r + j * M) (3 * M))
    (h : child P Q T F j f C = true) :
    Covered P Q (r + j * M) (3 * M) := by
  have hr := ext_sound P Q T F j r M f hf
  unfold child at h
  revert hr h
  cases ext P Q T F j f with
  | none => intro _ hr; exact hr
  | some g => intro h hr; exact ih g hr h

lemma cover_sound (P Q F : ℕ) : ∀ (Ts : List ℕ) (r M : ℕ) (f : List Ent), AllOK P Q r M f →
    cover P Q F Ts f = true → Covered P Q r M := by
  intro Ts
  induction Ts with
  | nil => intro r M f _ h; exact absurd h (by simp [cover])
  | cons T Ts ih =>
    intro r M f hf h
    have e : cover P Q F (T :: Ts) f = (nonempty f && child P Q T F 0 f (cover P Q F Ts) &&
      child P Q T F 1 f (cover P Q F Ts) && child P Q T F 2 f (cover P Q F Ts)) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, h0⟩, h1⟩, h2⟩ := h
    have c0 := covered_of_res (j := 0) hf (fun g hg hc => ih _ _ g hg hc) h0
    have c1 := covered_of_res (j := 1) hf (fun g hg hc => ih _ _ g hg hc) h1
    have c2 := covered_of_res (j := 2) hf (fun g hg hc => ih _ _ g hg hc) h2
    simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at c0 c1
    exact covered_split c0 c1 c2

/-- The class reached from `(r, M)` along the digits `js`. -/
def cls : ℕ → ℕ → List ℕ → ℕ × ℕ
  | r, M, [] => (r, M)
  | r, M, j :: js => cls (r + j * M) (3 * M) js

lemma covered_sub {P Q : ℕ} : ∀ (js : List ℕ) (r M : ℕ), r < M → (∀ j ∈ js, j < 3) →
    Covered P Q r M → Covered P Q (cls r M js).1 (cls r M js).2
  | [], _, _, _, _, h => h
  | j :: js, r, M, hr, hj, h => by
    have hj3 := hj j (List.mem_cons_self ..)
    apply covered_sub js (r + j * M) (3 * M) (by nlinarith) (fun i hi => hj i (List.mem_cons_of_mem _ hi))
    intro a ha
    apply h a
    rw [← Nat.mod_mod_of_dvd a (dvd_mul_left M 3), ha, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr]

lemma desc_sound (P Q F : ℕ) : ∀ (js Ts : List ℕ) (r M : ℕ) (f : List Ent), r < M →
    (∀ j ∈ js, j < 3) → AllOK P Q r M f → desc P Q F js Ts f = true →
    Covered P Q (cls r M js).1 (cls r M js).2 := by
  intro js
  induction js with
  | nil => intro Ts r M f _ _ hf h; exact cover_sound P Q F Ts r M f hf h
  | cons j js ih =>
    intro Ts r M f hr hj hf h
    have hj3 := hj j (List.mem_cons_self ..)
    have hr' : r + j * M < 3 * M := by nlinarith
    have hjs : ∀ i ∈ js, i < 3 := fun i hi => hj i (List.mem_cons_of_mem _ hi)
    cases Ts with
    | nil => exact absurd h (by simp [desc])
    | cons T Ts =>
      have e : desc P Q F (j :: js) (T :: Ts) f = child P Q T F j f (desc P Q F js Ts) := rfl
      rw [e] at h
      have hres := ext_sound P Q T F j r M f hf
      show Covered P Q (cls (r + j * M) (3 * M) js).1 (cls (r + j * M) (3 * M) js).2
      unfold child at h
      revert h hres
      cases ext P Q T F j f with
      | none => intro _ hres; exact covered_sub js _ _ hr' hjs hres
      | some g => intro h hres; exact ih Ts _ _ g hr' hjs hres h

/-- **Soundness of a chunk.** -/
theorem chunk_sound {P Q F r0 : ℕ} {js Ts : List ℕ} (hr0 : r0 = 1 ∨ r0 = 2) (hjs : ∀ j ∈ js, j < 3)
    (h : chunk P Q F r0 js Ts = true) : Covered P Q (cls r0 3 js).1 (cls r0 3 js).2 := by
  apply desc_sound P Q F js Ts r0 3 _ (by omega) hjs _ h
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  refine ⟨0, 0, by simp, fun t => ?_⟩
  simp [oddCount]

/-- `chunk_sound` with the digit condition as a `Bool` (provable by `rfl`), for generated files. -/
theorem chunk_sound' {P Q F r0 : ℕ} {js Ts : List ℕ} (hr0 : r0 = 1 ∨ r0 = 2)
    (hjs : js.all (fun j => Nat.blt j 3) = true) (h : chunk P Q F r0 js Ts = true) :
    Covered P Q (cls r0 3 js).1 (cls r0 3 js).2 :=
  chunk_sound hr0 (fun j hj => by simpa [Nat.blt_eq] using List.all_eq_true.mp hjs j hj) h

/-! ## Long stopping times -/

/-- Iterating codeword paths backwards from `4`. -/
lemma backward_AL {P Q : ℕ}
    (hc : ∀ a, a % 3 ≠ 0 → ∃ n k, 0 < k ∧ kstepT^[k] n = a ∧ n % 3 ≠ 0 ∧ P * k ≤ Q * oddCount k n) :
    ∀ N, ∃ n L, N ≤ L ∧ n % 3 ≠ 0 ∧ kstepT^[L] n = 4 ∧ P * L ≤ Q * oddCount L n
  | 0 => ⟨4, 0, le_rfl, by norm_num, rfl, by simp [oddCount]⟩
  | N + 1 => by
    obtain ⟨n, L, hN, hn3, hT, hP⟩ := backward_AL hc N
    obtain ⟨n', k, hk, hT', hn3', hP'⟩ := hc n hn3
    refine ⟨n', k + L, by omega, hn3', ?_, ?_⟩
    · rw [Nat.add_comm, Function.iterate_add_apply, hT', hT]
    · rw [oddCount_add, hT', Nat.mul_add, Nat.mul_add]; omega

/-- **Long stopping times from a covering.** If every unit ends a path of ratio `≥ P/Q`, then
for every `N` there is `n` with total stopping time exactly `L + 2 ≥ N + 2` and
`Q log n - 2 P log 3 ≤ (Q log 2 - P log 3) (L + 2)`. -/
theorem long_stopping_AL {P Q : ℕ}
    (hc : ∀ a, a % 3 ≠ 0 → ∃ n k, 0 < k ∧ kstepT^[k] n = a ∧ n % 3 ≠ 0 ∧ P * k ≤ Q * oddCount k n)
    (N : ℕ) : ∃ n L, N ≤ L ∧ 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
      Q * Real.log n - 2 * P * Real.log 3 ≤ (Q * Real.log 2 - P * Real.log 3) * (L + 2 : ℕ) := by
  obtain ⟨n, L, hN, -, hnT, hodd⟩ := backward_AL hc N
  have h4 : kstepT 4 = 2 := rfl
  have h2 : kstepT 2 = 1 := rfl
  have h1 : kstepT^[L + 2] n = 1 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hnT, h4, h2]
  have hne : ∀ i < L + 2, kstepT^[i] n ≠ 1 := by
    intro i hi h1
    rcases Nat.lt_or_ge i (L + 1) with hiL | hiL
    · have : kstepT^[L] n = kstepT^[L - i] 1 := by
        rw [← h1, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      rw [hnT] at this
      rcases iterate_one_mem (L - i) with h | h <;> omega
    · rw [show i = L + 1 by omega, Function.iterate_succ_apply', hnT, h4] at h1
      omega
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : kstepT^[L + 2] 0 = 0 := Function.iterate_fixed rfl _
      omega
    · exact h0
  refine ⟨n, L, hN, hn, h1, hne, ?_⟩
  have hsize : 3 ^ oddCount L n * n ≤ 2 ^ (L + 2) := by
    have := iterate_lower n L
    rw [hnT] at this
    calc 3 ^ oddCount L n * n ≤ 2 ^ L * 4 := this
      _ = 2 ^ (L + 2) := by ring
  set s := oddCount L n
  have hsR : ((3 : ℝ) ^ s * n) ≤ 2 ^ (L + 2) := by exact_mod_cast hsize
  have hl := Real.log_le_log (by positivity) hsR
  rw [Real.log_mul (by positivity) (by exact_mod_cast (show n ≠ 0 by omega)), Real.log_pow,
    Real.log_pow] at hl
  have hoddR : (P * L : ℝ) ≤ Q * s := by exact_mod_cast hodd
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQ : (0 : ℝ) ≤ Q := by positivity
  push_cast at hl ⊢
  nlinarith [mul_le_mul_of_nonneg_right hoddR h3.le, mul_le_mul_of_nonneg_left hl hQ]

/-- Units are covered once the two classes mod `3` are. -/
theorem units_of_covered {P Q : ℕ} (h1 : Covered P Q 1 3) (h2 : Covered P Q 2 3) :
    ∀ a, a % 3 ≠ 0 → ∃ n k, 0 < k ∧ kstepT^[k] n = a ∧ n % 3 ≠ 0 ∧ P * k ≤ Q * oddCount k n := by
  intro a ha
  rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h
  · exact h1 a h
  · exact h2 a h

/-! ## Example: the whole certificate for `α = 2/5` in two chunks -/

theorem ex25_1 : chunk 2 5 64 1 [] [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15] = true := by decide +kernel
theorem ex25_2 : chunk 2 5 64 2 [] [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15] = true := by decide +kernel

/-- `5 log n - 4 log 3 ≤ (5 log 2 - 2 log 3) σ(n)` for infinitely many `n` (`γ ≈ 3.94`), from the
kernel-run search with ratio `2/5`. -/
theorem long_stopping_AL_25 (N : ℕ) : ∃ n L, N ≤ L ∧ 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    (5 : ℕ) * Real.log n - 2 * (2 : ℕ) * Real.log 3 ≤
      ((5 : ℕ) * Real.log 2 - (2 : ℕ) * Real.log 3) * (L + 2 : ℕ) :=
  long_stopping_AL (units_of_covered (chunk_sound (Or.inl rfl) (by simp) ex25_1)
    (chunk_sound (Or.inr rfl) (by simp) ex25_2)) N

end Collatz.LSA
