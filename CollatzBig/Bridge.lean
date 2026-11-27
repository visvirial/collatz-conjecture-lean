import CollatzBig.All
import Collatz.NatCycles

/-!
# Periodic points from the 2^32 cycle bound

A positive integer that is a periodic point of the 2-adic map `T` and does not reach `1` has
`T`-period at least `125743`, the lower bound on the even steps of a nontrivial cycle.

Compiled by `scripts/assemble_big.sh` after `CollatzBig.All`.
-/

namespace CollatzBig

open Collatz

theorem kstepT_period_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (h : kstepT^[p] n = n)
    (hnr : ¬ ReachesOne n) : 125743 ≤ p :=
  Collatz.kstepT_period_ge (fun _ _ hc hr => evens_card_ge hc hr) hn hp h hnr

theorem natCast_periodic_ge {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (h : TwoAdic.T^[p] (n : ℤ_[2]) = n) (hnr : ¬ ReachesOne n) : 125743 ≤ p :=
  natCast_periodic_ge_of (fun _ _ hc hr => evens_card_ge hc hr) hn hp h hnr

end CollatzBig
