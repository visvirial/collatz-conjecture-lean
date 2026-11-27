import Collatz.LS12.C000
import Collatz.LS12.C001
import Collatz.LS12.C002
import Collatz.LS12.C003
import Collatz.LS12.C004
import Collatz.LS12.C005
import Collatz.LS12.C006
import Collatz.LS12.C007
import Collatz.LS12.C008
import Collatz.LS12.C009
import Collatz.LS12.C010
import Collatz.LS12.C011
import Collatz.LS12.C012
import Collatz.LS12.C013
import Collatz.LS12.C014
import Collatz.LS12.C015
import Collatz.LS12.C016
import Collatz.LS12.C017
import Collatz.LS12.C018
import Collatz.LS12.C019
import Collatz.LS12.C020
import Collatz.LS12.C021
import Collatz.LS12.C022
import Collatz.LS12.C023
import Collatz.LS12.C024
import Collatz.LS12.C025
import Collatz.LS12.C026
import Collatz.LS12.C027
import Collatz.LS12.C028
import Collatz.LS12.C029
import Collatz.LS12.C030
import Collatz.LS12.C031
import Collatz.LS12.C032
import Collatz.LS12.C033
import Collatz.LS12.C034
import Collatz.LS12.C035
import Collatz.LS12.C036
import Collatz.LS12.C037
import Collatz.LS12.C038
import Collatz.LS12.C039
import Collatz.LS12.Bound
import Collatz.LongStopGen

/-!
# Long trajectories mod `3^12`: `γ ≈ 5.38`

The instance of `Collatz.LongStopGen` with `M = 3^12`, `P/Q = 6/13` and `H = 73`
(`scripts/longstop_cert.py 12 6 13`, `scripts/gen_ls12.py`): the certificate condition is checked
by `decide +kernel` in the generated modules `Collatz/LS12/C*.lean`, which are combined here.
Infinitely many `n` reach `1` only after `σ(n) ≥ γ log n - c` steps,
`γ = 1 / (log 2 - (6/13) log 3) ≈ 5.38`.
-/

namespace Collatz.LS12

theorem all_ok : Collatz.kallFrom ok 0 1594323 = true := by
  have h := (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append (kallFrom_append chunk000 chunk001) chunk002) chunk003) chunk004) chunk005) chunk006) chunk007) chunk008) chunk009) chunk010) chunk011) chunk012) chunk013) chunk014) chunk015) chunk016) chunk017) chunk018) chunk019) chunk020) chunk021) chunk022) chunk023) chunk024) chunk025) chunk026) chunk027) chunk028) chunk029) chunk030) chunk031) chunk032) chunk033) chunk034) chunk035) chunk036) chunk037) chunk038) chunk039)
  norm_num at h
  exact h

theorem cert : LSCert pot 531441 6 13 := by
  intro t ht h3
  have := kallFrom_spec all_ok t (Nat.zero_le t) (by omega)
  simp only [ok, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at this
  omega

theorem pot_le : ∀ r < 531441, pot r ≤ 73 := by
  intro r hr
  simpa using kall_spec bound r hr

end Collatz.LS12

namespace Collatz

/-- **Infinitely many `n` need at least `≈ 5.38 log n` steps to reach `1`**:
`13 log n - 85 log 3 ≤ (13 log 2 - 6 log 3) σ(n)` with `σ(n) = L + 2` for every `L`. -/
theorem long_stopping_log_twelve (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    13 * Real.log n - 85 * Real.log 3 ≤ (13 * Real.log 2 - 6 * Real.log 3) * (L + 2 : ℕ) := by
  obtain ⟨n, h1, h2, h3, h4⟩ := long_stopping_log_gen (M := 531441) (P := 6) (Q := 13) (H := 73)
    (by norm_num) (by norm_num) LS12.cert LS12.pot_le L
  refine ⟨n, h1, h2, h3, ?_⟩
  norm_num at h4 ⊢
  linarith

end Collatz
