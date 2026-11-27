import Collatz.Bernoulli
import Collatz.Mixing

/-!
# The autoconjugacy of the 2-adic 3x+1 map

Following

* K. G. Monks, J. Yazinski, *The autoconjugacy of the 3x+1 function*,
  Discrete Math. 275 (2004) 219–236,

with the classification argument in the style of M. Monks (*Endomorphisms of the shift
dynamical system, discrete derivatives, and applications*) and of Edgington
(*The autoconjugacy of a generalized Collatz map*, arXiv:1206.0553).

Let `V y = -1 - y` (bitwise complement of binary digits) and
`Ω = Q⁻¹ ∘ V ∘ Q`, where `Q` is Lagarias' conjugacy (`Collatz.TwoAdic.Qequiv`).

Main results:
* `shift_V`: `shift (V y) = V (shift y)`;
* `T_Ω`: `T (Ω x) = Ω (T x)` (`Ω` is an autoconjugacy of `T`);
* `Ω_Ω`, `Ω_isometry`, `Ω_measurePreserving`: `Ω` is an involutive, isometric,
  Haar-measure-preserving bijection;
* `par_Ω`, `Ω_ne_self`: `Ω` flips parity, hence has no fixed point;
* `Ω_zero`, `Ω_neg_one`, `Ω_one`, `Ω_two`: `Ω 0 = -1`, `Ω (-1) = 0`, `Ω 1 = 2`, `Ω 2 = 1`;
* `solenoidal_commute_classification`: a solenoidal map `f : ℤ₂ → ℤ₂`
  (`2^k ∣ x - y → 2^k ∣ f x - f y`) with `T ∘ f = f ∘ T` is one of `id`, `Ω`,
  `fun _ => 0`, `fun _ => -1`; `solenoidal_commute_iff` gives the converse too;
* `solenoidal_bijective_autoconjugacy`: the only solenoidal bijective (indeed: injective)
  autoconjugacies of `T` are `id` and `Ω` (the Monks–Yazinski uniqueness statement).

No weakening of the stated results was necessary.
-/

namespace Collatz.TwoAdic

open PadicInt

/-! ## The complement map `V` -/

/-- Bitwise complement on `ℤ₂`: `V y = -1 - y`. -/
noncomputable def V (y : ℤ_[2]) : ℤ_[2] := -1 - y

lemma V_V (y : ℤ_[2]) : V (V y) = y := by unfold V; ring

lemma par_cases (y : ℤ_[2]) : par y = 0 ∨ par y = 1 := by have := par_lt y; omega

/-- `V y = (1 - par y) + 2 * V (shift y)`. -/
lemma V_eq (y : ℤ_[2]) : V y = ((1 - par y : ℕ) : ℤ_[2]) + 2 * V (shift y) := by
  have e := eq_par_add_shift y
  unfold V
  rcases par_cases y with h | h <;> rw [h] at e ⊢ <;> norm_num at e ⊢ <;>
    linear_combination -e

lemma par_V (y : ℤ_[2]) : par (V y) = 1 - par y := by
  rw [V_eq, par_add_two_mul, par_natCast]; omega

theorem shift_V (y : ℤ_[2]) : shift (V y) = V (shift y) := by
  apply half_eq
  rw [par_V]
  conv_rhs => rw [V_eq y]
  ring

lemma V_isometry : Isometry V := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← norm_neg]
  unfold V; congr 1; ring

/-- `V` as an isometric equivalence. -/
noncomputable def Vequiv : ℤ_[2] ≃ᵢ ℤ_[2] :=
  IsometryEquiv.mk ⟨V, V, V_V, V_V⟩ V_isometry

/-! ## The autoconjugacy `Ω` -/

/-- The Monks–Yazinski autoconjugacy as an isometric equivalence: `Q⁻¹ ∘ V ∘ Q`. -/
noncomputable def Ωequiv : ℤ_[2] ≃ᵢ ℤ_[2] := (Qequiv.trans Vequiv).trans Qequiv.symm

/-- The Monks–Yazinski autoconjugacy `Ω = Q⁻¹ ∘ V ∘ Q`. -/
noncomputable def Ω (x : ℤ_[2]) : ℤ_[2] := Qequiv.symm (V (Qequiv x))

lemma Ωequiv_apply (x : ℤ_[2]) : Ωequiv x = Ω x := rfl

lemma coe_Ωequiv : (Ωequiv : ℤ_[2] → ℤ_[2]) = Ω := rfl

lemma Qequiv_apply (x : ℤ_[2]) : Qequiv x = Q x := rfl

lemma Qequiv_Ω (x : ℤ_[2]) : Qequiv (Ω x) = V (Qequiv x) := by
  simp [Ω]

/-- **Autoconjugacy** (Monks–Yazinski): `T ∘ Ω = Ω ∘ T`. -/
theorem T_Ω (x : ℤ_[2]) : T (Ω x) = Ω (T x) := by
  apply Qequiv.injective
  rw [Qequiv_conj, Qequiv_Ω, Qequiv_Ω, Qequiv_conj, shift_V]

theorem Ω_Ω (x : ℤ_[2]) : Ω (Ω x) = x := by
  apply Qequiv.injective
  rw [Qequiv_Ω, Qequiv_Ω, V_V]

theorem Ω_involutive : Function.Involutive Ω := Ω_Ω

theorem Ω_isometry : Isometry Ω := Ωequiv.isometry

theorem Ω_measurePreserving : MeasureTheory.MeasurePreserving Ω μ μ :=
  measurePreserving_isometryEquiv Ωequiv

/-- `Ω` flips parity. -/
theorem par_Ω (x : ℤ_[2]) : par (Ω x) = 1 - par x := by
  rw [← par_Q (Ω x), ← Qequiv_apply, Qequiv_Ω, par_V, Qequiv_apply, par_Q]

theorem Ω_ne_self (x : ℤ_[2]) : Ω x ≠ x := by
  intro h
  have := par_Ω x
  rw [h] at this
  rcases par_cases x with h' | h' <;> omega

/-! ## Values of `Ω` -/

lemma par_zero' : par (0 : ℤ_[2]) = 0 := by simpa using par_natCast 0

lemma par_one' : par (1 : ℤ_[2]) = 1 := by simpa using par_natCast 1

lemma par_neg_one : par (-1 : ℤ_[2]) = 1 := by
  have := par_add_two_mul 1 (-1)
  rw [show (1 : ℤ_[2]) + 2 * -1 = -1 by ring, par_one'] at this
  exact this

lemma T_zero : T 0 = 0 := half_eq (by rw [par_zero']; ring)

lemma T_neg_one : T (-1) = -1 := half_eq (by rw [par_neg_one]; push_cast; ring)

lemma T_one : T 1 = 2 := half_eq (by rw [par_one']; push_cast; ring)

lemma T_two : T 2 = 1 := by
  have h2 : par (2 : ℤ_[2]) = 0 := by simpa using par_natCast 2
  exact half_eq (by rw [h2]; push_cast; ring)

lemma Q_zero : Q 0 = 0 := by
  have := Q_rec 0
  rw [par_zero', T_zero] at this
  push_cast at this
  linear_combination -this

lemma Q_neg_one : Q (-1) = -1 := by
  have := Q_rec (-1)
  rw [par_neg_one, T_neg_one] at this
  push_cast at this
  linear_combination -this

lemma Qequiv_symm_zero : Qequiv.symm 0 = 0 := by
  rw [IsometryEquiv.symm_apply_eq, Qequiv_apply, Q_zero]

lemma Qequiv_symm_neg_one : Qequiv.symm (-1) = -1 := by
  rw [IsometryEquiv.symm_apply_eq, Qequiv_apply, Q_neg_one]

theorem Ω_zero : Ω 0 = -1 := by
  rw [Ω, Qequiv_apply, Q_zero, show V 0 = -1 by unfold V; ring, Qequiv_symm_neg_one]

theorem Ω_neg_one : Ω (-1) = 0 := by rw [← Ω_zero, Ω_Ω]

theorem Ω_one : Ω 1 = 2 := by
  have h1 := Q_rec 1
  have h2 := Q_rec 2
  have hp2 : par (2 : ℤ_[2]) = 0 := by simpa using par_natCast 2
  rw [par_one', T_one] at h1
  rw [hp2, T_two] at h2
  push_cast at h1 h2
  rw [Ω, IsometryEquiv.symm_apply_eq, Qequiv_apply, Qequiv_apply]
  unfold V
  linear_combination h1 + h2

theorem Ω_two : Ω 2 = 1 := by rw [← Ω_one, Ω_Ω]

/-! ## Bits -/

lemma bits_zero_eq_iff (x : ℤ_[2]) (b : Bool) : bits x 0 = b ↔ par x = if b then 1 else 0 := by
  simp only [bits, Function.iterate_zero, id]
  rcases par_cases x with h | h <;> cases b <;> simp [h]

lemma par_eq_of_bits_zero {x y : ℤ_[2]} (h : bits x 0 = bits y 0) : par x = par y := by
  have hx := (bits_zero_eq_iff x (bits x 0)).1 rfl
  have hy := (bits_zero_eq_iff y (bits y 0)).1 rfl
  rw [hx, hy, h]

lemma two_dvd_of_par_eq {x y : ℤ_[2]} (h : par x = par y) : (2 : ℤ_[2]) ∣ x - y :=
  ⟨shift x - shift y, by
    rw [mul_sub, two_mul_shift, two_mul_shift, h]; ring⟩

lemma bits_bv_zero (b : Bool) : bits (bv b) 0 = b := by
  rw [bits_zero_eq_iff, par_bv]

lemma bits_V (y : ℤ_[2]) (i : ℕ) : bits (V y) i = !bits y i := by
  induction i generalizing y with
  | zero =>
    have hy := (bits_zero_eq_iff y (bits y 0)).1 rfl
    rw [bits_zero_eq_iff, par_V, hy]
    cases bits y 0 <;> simp
  | succ i ih => rw [bits_succ, bits_succ, shift_V, ih]

lemma bits_injective : Function.Injective bits := by
  intro x y h
  rw [← ofBits_bits x, ← ofBits_bits y, h]

lemma ofBits_false : ofBits (fun _ => false) = 0 := by
  simp [ofBits, bv]

lemma bits_zero_fun : bits 0 = fun _ => false := by
  rw [← ofBits_false, bits_ofBits]

lemma bits_neg_one_fun : bits (-1) = fun _ => true := by
  funext i
  rw [show (-1 : ℤ_[2]) = V 0 by unfold V; ring, bits_V, bits_zero_fun]
  rfl

/-! ## Classification of solenoidal autoconjugacies -/

/-- `f` is solenoidal: it respects congruences modulo every power of `2`
(equivalently, `f` is `1`-Lipschitz). -/
def Solenoidal (f : ℤ_[2] → ℤ_[2]) : Prop :=
  ∀ (k : ℕ) (x y : ℤ_[2]), (2 : ℤ_[2]) ^ k ∣ x - y → (2 : ℤ_[2]) ^ k ∣ f x - f y

lemma Solenoidal.of_isometry {f : ℤ_[2] → ℤ_[2]} (hf : Isometry f) : Solenoidal f := by
  intro k x y h
  rw [← norm_le_iff_dvd, ← dist_eq_norm, hf.dist_eq, dist_eq_norm, norm_le_iff_dvd]
  exact h

lemma solenoidal_const (c : ℤ_[2]) : Solenoidal (fun _ => c) := by
  intro k x y _; simp

/-- The shift-side map `Q ∘ f ∘ Q⁻¹`. -/
noncomputable def conjQ (f : ℤ_[2] → ℤ_[2]) (y : ℤ_[2]) : ℤ_[2] := Qequiv (f (Qequiv.symm y))

lemma eq_of_conjQ (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : f x = Qequiv.symm (conjQ f (Qequiv x)) := by
  simp [conjQ]

lemma Qequiv_dvd_iff (k : ℕ) (x y : ℤ_[2]) :
    (2 : ℤ_[2]) ^ k ∣ Qequiv x - Qequiv y ↔ (2 : ℤ_[2]) ^ k ∣ x - y :=
  pow_dvd_Q_sub_iff k x y

lemma conjQ_solenoidal {f : ℤ_[2] → ℤ_[2]} (hf : Solenoidal f) : Solenoidal (conjQ f) := by
  intro k x y h
  rw [conjQ, conjQ, Qequiv_dvd_iff]
  apply hf
  rw [← Qequiv_dvd_iff]
  simpa using h

lemma conjQ_shift {f : ℤ_[2] → ℤ_[2]} (hT : ∀ x, T (f x) = f (T x)) (y : ℤ_[2]) :
    conjQ f (shift y) = shift (conjQ f y) := by
  have e : Qequiv.symm (shift y) = T (Qequiv.symm y) := (T_iterate_symm 1 y).symm
  rw [conjQ, conjQ, e, ← hT, Qequiv_conj]

/-- The core classification on the shift side: a solenoidal map commuting with the shift
acts bitwise through a single map `Bool → Bool`. -/
theorem bits_of_solenoidal_shift {g : ℤ_[2] → ℤ_[2]} (hg : Solenoidal g)
    (hs : ∀ y, g (shift y) = shift (g y)) (y : ℤ_[2]) (i : ℕ) :
    bits (g y) i = bits (g (bv (bits y i))) 0 := by
  induction i generalizing y with
  | zero =>
    apply (bits_zero_eq_iff _ _).2
    rw [← (bits_zero_eq_iff _ _).1 rfl]
    apply par_eq_of_two_dvd
    have h := two_dvd_of_par_eq (par_eq_of_bits_zero (bits_bv_zero (bits y 0)).symm)
    simpa using hg 1 _ _ h
  | succ i ih => rw [bits_succ, ← hs, ih, bits_succ]

theorem solenoidal_shift_classification {g : ℤ_[2] → ℤ_[2]} (hg : Solenoidal g)
    (hs : ∀ y, g (shift y) = shift (g y)) :
    g = id ∨ g = V ∨ g = (fun _ => 0) ∨ g = (fun _ => -1) := by
  have key := bits_of_solenoidal_shift hg hs
  set h : Bool → Bool := fun b => bits (g (bv b)) 0 with hh
  have key' : ∀ y i, bits (g y) i = h (bits y i) := key
  rcases hf : h false <;> rcases ht : h true
  · -- constant `false`
    right; right; left
    funext y; apply bits_injective; funext i
    rw [key', bits_zero_fun]; cases bits y i <;> assumption
  · -- identity
    left
    funext y; apply bits_injective; funext i
    rw [key']; cases hb : bits y i <;> simp [hf, ht, hb]
  · -- complement
    right; left
    funext y; apply bits_injective; funext i
    rw [key', bits_V]; cases hb : bits y i <;> simp [hf, ht]
  · -- constant `true`
    right; right; right
    funext y; apply bits_injective; funext i
    rw [key', bits_neg_one_fun]; cases bits y i <;> assumption

/-- **Classification** (Monks–Yazinski): a solenoidal map commuting with `T` is `id`, `Ω`,
or one of the constants `0`, `-1`. -/
theorem solenoidal_commute_classification {f : ℤ_[2] → ℤ_[2]} (hf : Solenoidal f)
    (hT : ∀ x, T (f x) = f (T x)) :
    f = id ∨ f = Ω ∨ f = (fun _ => 0) ∨ f = (fun _ => -1) := by
  rcases solenoidal_shift_classification (conjQ_solenoidal hf) (conjQ_shift hT) with
    h | h | h | h
  · left; funext x; rw [eq_of_conjQ f x, h]; simp
  · right; left; funext x; rw [eq_of_conjQ f x, h]; rfl
  · right; right; left; funext x; rw [eq_of_conjQ f x, h]; exact Qequiv_symm_zero
  · right; right; right; funext x; rw [eq_of_conjQ f x, h]; exact Qequiv_symm_neg_one

/-- The four maps of the classification are indeed solenoidal autoconjugacies. -/
theorem solenoidal_commute_iff (f : ℤ_[2] → ℤ_[2]) :
    (Solenoidal f ∧ ∀ x, T (f x) = f (T x)) ↔
      f = id ∨ f = Ω ∨ f = (fun _ => 0) ∨ f = (fun _ => -1) := by
  refine ⟨fun h => solenoidal_commute_classification h.1 h.2, ?_⟩
  rintro (rfl | rfl | rfl | rfl)
  · exact ⟨Solenoidal.of_isometry isometry_id, fun _ => rfl⟩
  · exact ⟨Solenoidal.of_isometry Ω_isometry, T_Ω⟩
  · exact ⟨solenoidal_const 0, fun _ => T_zero⟩
  · exact ⟨solenoidal_const (-1), fun _ => T_neg_one⟩

/-- **Uniqueness** (Monks–Yazinski): `id` and `Ω` are the only solenoidal injective
(in particular, bijective) maps commuting with `T`. -/
theorem solenoidal_injective_autoconjugacy {f : ℤ_[2] → ℤ_[2]} (hf : Solenoidal f)
    (hT : ∀ x, T (f x) = f (T x)) (hi : Function.Injective f) : f = id ∨ f = Ω := by
  rcases solenoidal_commute_classification hf hT with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have := @hi 0 1 (by rw [h])
    exact zero_ne_one this
  · exfalso
    have := @hi 0 1 (by rw [h])
    exact zero_ne_one this

theorem solenoidal_bijective_autoconjugacy {f : ℤ_[2] → ℤ_[2]} (hf : Solenoidal f)
    (hT : ∀ x, T (f x) = f (T x)) (hb : Function.Bijective f) : f = id ∨ f = Ω :=
  solenoidal_injective_autoconjugacy hf hT hb.1

end Collatz.TwoAdic

/-! ## Axioms -/

/-- info: 'Collatz.TwoAdic.shift_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.shift_V

/-- info: 'Collatz.TwoAdic.T_Ω' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.T_Ω

/-- info: 'Collatz.TwoAdic.Ω_Ω' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_Ω

/-- info: 'Collatz.TwoAdic.Ω_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_isometry

/-- info: 'Collatz.TwoAdic.Ω_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_measurePreserving

/-- info: 'Collatz.TwoAdic.par_Ω' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.par_Ω

/-- info: 'Collatz.TwoAdic.Ω_ne_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_ne_self

/-- info: 'Collatz.TwoAdic.Ω_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_zero

/-- info: 'Collatz.TwoAdic.Ω_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_neg_one

/-- info: 'Collatz.TwoAdic.Ω_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_one

/-- info: 'Collatz.TwoAdic.Ω_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.Ω_two

/-- info: 'Collatz.TwoAdic.solenoidal_commute_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.solenoidal_commute_classification

/-- info: 'Collatz.TwoAdic.solenoidal_commute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.solenoidal_commute_iff

/-- info: 'Collatz.TwoAdic.solenoidal_injective_autoconjugacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.solenoidal_injective_autoconjugacy

/-- info: 'Collatz.TwoAdic.solenoidal_bijective_autoconjugacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Collatz.TwoAdic.solenoidal_bijective_autoconjugacy
