import CollatzBig.All
import CollatzBig.Cst0
import CollatzBig.Cst1
import CollatzBig.Cst2
import CollatzBig.Cst3
import Collatz.CoeffStop

/-!
# Terras' coefficient stopping time conjecture up to level 125742

Every `n ≥ 2` whose coefficient `3^(s_j)/2^j` drops below `1` at some `j < 125743` drops below
itself within `j` steps. Three ranges (`Collatz.cst_of_tables`):
* `n < 2^17`: direct kernel check (`Cst0`-`Cst3`);
* `2^17 ≤ n < 2^32`: the 2^32 verification bounds the stopping time by `1000`, so `s ≤ 630`,
  which `cycCheck2 (2^17)` excludes up to `971`;
* `n ≥ 2^32`: `cycCheck2 (2^32)` excludes `s < 79335`, and `j ≤ 125742` forces `s ≤ 79334`.

Hence for `k < 125743` the integers `n ≥ 2` with stopping time `≤ k` are exactly the residue
classes of `goodSet k` (Terras' periodicity, with no exceptions).
Compiled by `scripts/assemble_big.sh` after `CollatzBig.All`.
-/

namespace CollatzBig

open Collatz Finset

theorem cstSmall : kallFrom (cstCheck 1000) 0 131072 = true := by
  have h01 := kallFrom_append (f := cstCheck 1000) (lo := 0) (l1 := 32768) (l2 := 32768) cst0 cst1
  have h23 := kallFrom_append (f := cstCheck 1000) (lo := 65536) (l1 := 32768) (l2 := 32768)
    cst2 cst3
  exact kallFrom_append (f := cstCheck 1000) (lo := 0) (l1 := 65536) (l2 := 65536) h01 h23

theorem cyc17 : kall (cycCheck2 131072) 971 = true := by decide +kernel

lemma pow_bound_small : 2 ^ 999 < 3 ^ 631 := by decide +kernel
lemma pow_bound_large : 2 ^ 125742 < 3 ^ 79335 := by decide +kernel

/-- **Coefficient stopping time conjecture up to level 125742.** -/
theorem stops_at_coeff_stop {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) (hJ : j < 125743)
    (h : 3 ^ oddCount j n < 2 ^ j) : ∃ i, 1 ≤ i ∧ i ≤ j ∧ kstepT^[i] n < n := by
  have hmid := kstepT_descends_of_resCheck (k := 24) (M := 256) (fuel := 1000)
    (fun r hr => kall_of_kallFrom resAll r (by norm_num at hr ⊢; omega))
  refine cst_of_tables (fuel := 1000) (F := 1000) (N0 := 131072) (N1 := 4294967296)
    (B0 := 971) (B1 := 79335) (by norm_num) (by norm_num)
    (fun n h2 hlt => kallFrom_spec cstSmall n (by omega) (by omega))
    (fun n h2 hlt => by
      obtain ⟨i, hi, hiF, hd⟩ := hmid n h2 (by norm_num; omega)
      exact ⟨i, hi, by simpa using hiF, hd⟩)
    cyc17 (kall_of_kallFrom_zero cycAll) ?_ hn hj h ?_
  · intro s j' h3 hj'
    have : 3 ^ s < 3 ^ 631 :=
      lt_of_lt_of_le h3 (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) pow_bound_small.le)
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    omega
  · have : 3 ^ oddCount j n < 3 ^ 79335 :=
      lt_of_lt_of_le h (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        pow_bound_large.le)
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this

/-- **Terras' periodicity without exceptions**: for `k < 125743` and `n ≥ 2`, `n` has stopping
time `≤ k` iff its residue mod `2^k` lies in `goodSet k`. -/
theorem stopsBy_iff_goodSet {k n : ℕ} (hk : k < 125743) (hn : 2 ≤ n) :
    (∃ j ∈ Icc 1 k, kstepT^[j] n < n) ↔ n % 2 ^ k ∈ goodSet k := by
  constructor
  · rintro ⟨j, hj, hd⟩
    rw [mem_Icc] at hj
    simp only [goodSet, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ (by positivity), j, mem_Icc.2 hj, stopsBy_imp hj.2 hd⟩
  · intro hg
    simp only [goodSet, mem_filter, mem_range] at hg
    obtain ⟨-, j, hj, h3⟩ := hg
    rw [mem_Icc] at hj
    rw [← oddCount_mod hj.2] at h3
    obtain ⟨i, hi, hij, hd⟩ := stops_at_coeff_stop hn hj.1 (by omega) h3
    exact ⟨i, mem_Icc.2 ⟨hi, by omega⟩, hd⟩

end CollatzBig
