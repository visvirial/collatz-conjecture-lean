import Collatz.Defs

/-!
# Kernel check for the coefficient stopping time (no Mathlib)

`cstRun n0 fuel x p3 p2` follows the accelerated orbit from `x = T^j n` with `p3 = 3^(s_j)`,
`p2 = 2^j` and returns `true` iff at the first later `j` with `3^(s_j) < 2^j` (the coefficient
stopping time) the orbit is below `n0`. Kept separate from `Collatz.Defs` so that changing it
does not invalidate the `CollatzBig` chunks.
-/

namespace Collatz

def cstRun (n0 : Nat) (fuel : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ _ => false)
    (fun _ rec x p3 p2 =>
      bif (bif x % 2 == 0 then p3 else 3 * p3).blt (2 * p2) then (kstepT x).blt n0
      else rec (kstepT x) (bif x % 2 == 0 then p3 else 3 * p3) (2 * p2)) fuel

/-- `n` stops (drops below itself) exactly at its coefficient stopping time. -/
def cstCheck (fuel n : Nat) : Bool := n.blt 2 || cstRun n fuel n 1 1

end Collatz
