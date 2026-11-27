import Collatz.Defs

/-!
# Fast kernel checks for long-stopping-time potentials (no Mathlib)

Kernel-evaluated definitions for `Collatz.LongStopFast`. The potential on the residues mod `M`
is stored in pieces of `S` entries with `W` bits each; `pc i` is piece `i`. The certificate
condition of `Collatz.LSCert` is checked once per *source* residue `s < M` prime to `3` instead
of once per `t < 3M`: the three lifts `t = s + kM` share the even target `2t % M = 2s % M`, and
differ only in the odd target `(2t - 1)/3 % M`. The loops run over `q` and check `s = 3q + 1`
and `s = 3q + 2`.

The kernel re-evaluates an expression like `pc (r / S)` from scratch for every `r` (it caches
`whnf` only on syntactically equal terms), which made the lookup `List.getD` dominate the cost of
`Collatz.LS12`. Here the checked range is split into *runs* on which every lookup stays inside a
fixed piece, whose index is a literal of the run: then `pc a` is evaluated once per run and
cached. The run checker `okAt` verifies that each index really lies in the claimed piece, so a
wrong run list can only make the check fail.
-/

namespace Collatz.LSF

/-! All arithmetic is written with the bare functions `Nat.add`, `Nat.mod`, `Nat.beq`, ... rather
than `+`, `%`, `==`: this saves the kernel the instance unfolding at every operation (about a
factor two here). `Collatz.LongStopFast` restates the definitions with the usual notation. -/

/-- Entry `r % S` of the packed piece `B` (`W` bits per entry). -/
def ent (S W B r : Nat) : Nat := Nat.mod (Nat.shiftRight B (Nat.mul W (Nat.mod r S))) (Nat.pow 2 W)

/-- The potential: entry `r % S` of piece `pc (r / S)`. -/
def pot (pc : Nat → Nat) (S W r : Nat) : Nat := ent S W (pc (Nat.div r S)) r

/-- One odd lift: the target `o` lies in piece `c` (stored in `B`) and `hs ≤ h o + Q`. -/
def oddOk (S W Q hs B c o : Nat) : Bool := Nat.beq (Nat.div o S) c && Nat.ble hs (Nat.add (ent S W B o) Q)

/-- The certificate condition at the source `s < M`, with the pieces `Bs`, `Be`, `B0`, `B1`,
`B2` (claimed indices `a`, `b`, `c0`, `c1`, `c2`) holding `s`, the even target `2s % M`, and the
odd targets `(2(s + kM) - 1)/3 % M` of the three lifts. -/
def okAt (S W M P Q Bs a Be b B0 c0 B1 c1 B2 c2 s : Nat) : Bool :=
    (Nat.beq (Nat.div s S) a &&
      ((Nat.beq (Nat.div (Nat.mod (Nat.mul 2 s) M) S) b &&
          Nat.ble (Nat.add (ent S W Bs s) P) (ent S W Be (Nat.mod (Nat.mul 2 s) M))) ||
        ((Nat.beq (Nat.mod s 9) 2 || Nat.beq (Nat.mod s 9) 8) &&
          oddOk S W Q (Nat.add (ent S W Bs s) P) B0 c0
            (Nat.mod (Nat.div (Nat.sub (Nat.mul 2 s) 1) 3) M) &&
          oddOk S W Q (Nat.add (ent S W Bs s) P) B1 c1
            (Nat.mod (Nat.div (Nat.sub (Nat.mul 2 (Nat.add s M)) 1) 3) M) &&
          oddOk S W Q (Nat.add (ent S W Bs s) P) B2 c2
            (Nat.mod (Nat.div (Nat.sub (Nat.mul 2 (Nat.add s (Nat.mul 2 M))) 1) 3) M))))

/-- `kfrom f g lo len = true` iff `f (3q + 1) = true` and `g (3q + 2) = true` for all
`lo ≤ q < lo + len`. -/
def kfrom (f g : Nat → Bool) (lo len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => f (Nat.add (Nat.mul 3 (Nat.add lo i)) 1) &&
      g (Nat.add (Nat.mul 3 (Nat.add lo i)) 2) && acc) len

/-- A run: its length (in steps of `3` residues) and the piece indices `(a, b1, b2, c0, c1, c2)`
of the source, the even targets of `s = 3q + 1` and `s = 3q + 2`, and the odd targets (which
occur only for `s ≡ 2 (mod 3)`). -/
abbrev Run := Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- Check consecutive runs starting at `q = lo` (the residues `s` from `3 lo` on). -/
def runsOk (pc : Nat → Nat) (S W M P Q : Nat) : List Run → Nat → Bool
  | [], _ => true
  | (len, a, b1, b2, c0, c1, c2) :: rs, lo =>
    kfrom (okAt S W M P Q (pc a) a (pc b1) b1 (pc c0) c0 (pc c1) c1 (pc c2) c2)
      (okAt S W M P Q (pc a) a (pc b2) b2 (pc c0) c0 (pc c1) c1 (pc c2) c2) lo len &&
      runsOk pc S W M P Q rs (Nat.add lo len)

/-- The total length of a list of runs. -/
def runsLen : List Run → Nat
  | [] => 0
  | (len, _) :: rs => len + runsLen rs

end Collatz.LSF
