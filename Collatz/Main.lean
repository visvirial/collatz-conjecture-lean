import Collatz.Verify

/-!
# Main reduction theorem

The Collatz conjecture is equivalent to: every `n ≥ 2^10` lying in one of the 64 surviving
residue classes mod `2^10` descends. All other cases (all `n < 2^10`, and the other 960
residue classes) are proved here.
-/

namespace Collatz

theorem survivors_ten_length : (survivors 10).length = 64 := by decide +kernel

theorem conjecture_iff_survivors_descend :
    Conjecture ↔ ∀ n, 2 ^ 10 ≤ n → n % 2 ^ 10 ∈ survivors 10 → Descends n := by
  rw [conjecture_iff_descends]
  constructor
  · intro h n hn _
    exact h n (le_trans (by norm_num) hn)
  · intro h n hn
    rcases Nat.lt_or_ge n (2 ^ 10) with hlt | hge
    · exact descends_small n hn hlt
    · exact descends_large_of_survivors 10 h n hge

end Collatz
