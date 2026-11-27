import Collatz.Defs

/-!
# Kernel checker for extending the residue verification (no Mathlib)

`Collatz.Defs` (and hence the `CollatzBig` chunks for `n < 2^24 * 256`) is left unchanged; this
file adds a checker for the further range `2^k * M0 ≤ n < 2^k * M1`, `k = j0 + d`.

`resExt j0 d M0 M1 fuel r` (for `r < 2^j0`) walks the binary tree of residue classes below `r`:
at a node `(j, r)` (the class `r` mod `2^j`) it tries `cert j r`, which covers every `n ≥ 2^j` of
the class; otherwise it splits into the classes `r` and `r + 2^j` mod `2^(j+1)`. At depth `d`
(level `k`) the remaining survivors are checked directly with `kdesc` for every
`n = 2^k m + r`, `M0 ≤ m < M1`. Certified subtrees cost one `cert` evaluation, so most of the
`2^k` residues are never visited. Soundness is `Collatz.descends_of_resExt` in
`Collatz.ExtKernel`.
-/

namespace Collatz

/-- Sieve of depth `d` below the class `r` mod `2^j` (see the module docstring). -/
def sieveExt (M0 M1 fuel : Nat) (d : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun j r => cert j r ||
      kallFrom (fun m => kdesc (2 ^ j * m + r) fuel (2 ^ j * m + r)) M0 (M1 - M0))
    (fun _ rec j r => cert j r || (rec (j + 1) r && rec (j + 1) (r + 2 ^ j))) d

/-- Extension check for the top-level class `r` mod `2^j0`, down to level `j0 + d`. -/
def resExt (j0 d M0 M1 fuel r : Nat) : Bool := sieveExt M0 M1 fuel d j0 r

end Collatz
