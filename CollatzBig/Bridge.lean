import CollatzBig.All
import Collatz.NatCycles

/-!
# Periodic points from the 2^32 cycle bound

A positive integer that is a periodic point of the 2-adic map `T` and does not reach `1` has
`T`-period at least `102539` (half the cycle length bound `205078`).

Compile after `CollatzBig.All` with `lake env lean -o .lake/build/lib/lean/CollatzBig/Bridge.olean
CollatzBig/Bridge.lean`.
-/

namespace CollatzBig

open Collatz

theorem kstepT_period_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : kstepT^[p] n = n)
    (hnr : ¬ ReachesOne n) : 102539 ≤ p := by
  have := Collatz.kstepT_period_ge (L := 205078) (fun _ _ hc hr => cycle_length_ge hc hr)
    hn hp h hnr
  omega

theorem natCast_periodic_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : TwoAdic.T^[p] (n : ℤ_[2]) = n) (hnr : ¬ ReachesOne n) : 102539 ≤ p := by
  have := natCast_periodic_ge_of (L := 205078) (fun _ _ hc hr => cycle_length_ge hc hr)
    hn hp h hnr
  omega

end CollatzBig
