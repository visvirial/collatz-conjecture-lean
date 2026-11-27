/-!
# Applegate–Lagarias tree search in the kernel (no Mathlib)

Kernel-evaluated definitions for `Collatz.LongStopAL`. Instead of storing an Applegate–Lagarias
certificate (a ternary prefix code of residue classes of `3`-adic units, each with a backward
path of ratio `≥ P/Q`), the kernel re-runs the search.

A class is `a ≡ r (mod 3^m)`. Its *frontier* is a list of entries `(x, p, d)`: nodes of the
backward tree of the representative `r` reached by a path of length `k` with `w = m - 1` odd
moves, the last move odd, with `p = 2^k` and deficit `d = P k - Q w > 0`. The element
`r + 3^m t` of the class has the node `x + 3 p t` on the same path. For the child class
`r + j 3^m` the node becomes `x + 3 j p`; its even chain `2^i (x + 3 j p)` yields an odd child
`((2y - 1)/3, 2^(i+1) p, d + (i+1) P - Q)` at every chain node `y ≡ 2, 8 (mod 9)`. The child
class is closed (a codeword) as soon as some odd child has `d + (i+1) P ≤ Q`, i.e. ratio
`≥ P/Q`. Entries with deficit `> T` (the band, a per-level hint list) are dropped: hints can
only make the check fail, never succeed wrongly.

All arithmetic uses the bare `Nat.*` functions (see `Collatz.LSF`), loops are explicit
recursors.
-/

namespace Collatz.LSA

-- `List.rec` has no compiled code; these definitions are only evaluated by the kernel.
noncomputable section

/-- A frontier entry `(x, p, d)`. -/
abbrev Ent := Nat × Nat × Nat

/-- On the even chain `2^i y` of a unit `y`, the nodes `≡ 2, 8 (mod 9)` (those with an odd
move) are `i0, ...` with `i0 (y % 9)` packed with two bits per residue in `51460` (`2` has
order `6` mod `9`). -/
def i0 (u : Nat) : Nat := Nat.mod (Nat.shiftRight 51460 (Nat.mul 2 u)) 4

/-- `y % 9 ∈ {2, 8}`: the odd backward move `(2y - 1)/3` exists and is prime to `3`. -/
def oddOk (y : Nat) : Bool := Nat.beq (Nat.mod y 9) 2 || Nat.beq (Nat.mod y 9) 8

/-- The odd moves along the even chain from the node `y` (with `p`, deficit `d`), at most
`fuel` of them. From `y ≡ 2` the next node with an odd move is `4y ≡ 8`, from `y ≡ 8` it is
`16y ≡ 2 (mod 9)`. `none`: an odd child has ratio `≥ P/Q` (closed). `some acc`: the odd
children with deficit `≤ T` consed onto `acc`. The chain stops at a node without odd move
(which never happens for the nodes produced by `node`). -/
def chain (P Q T : Nat) (fuel : Nat) : Nat → Nat → Nat → List Ent → Option (List Ent) :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Ent → Option (List Ent))
    (fun _ _ _ acc => some acc)
    (fun _ ih y p d acc =>
      bif oddOk y then
        (bif Nat.ble (Nat.add d P) Q then none
         else bif Nat.ble (Nat.add d P) (Nat.add Q T) then
           ih (Nat.shiftLeft y (bif Nat.beq (Nat.mod y 9) 2 then 2 else 4))
             (Nat.shiftLeft p (bif Nat.beq (Nat.mod y 9) 2 then 2 else 4))
             (Nat.add d (Nat.mul (bif Nat.beq (Nat.mod y 9) 2 then 2 else 4) P))
             ((Nat.div (Nat.sub (Nat.mul 2 y) 1) 3, Nat.mul 2 p, Nat.sub (Nat.add d P) Q) :: acc)
         else some acc)
      else some acc)
    fuel

/-- Process the node `x` (with `p`, deficit `d`): jump to the first node of its even chain
with an odd move. -/
def node (P Q T F x p d : Nat) (acc : List Ent) : Option (List Ent) :=
  chain P Q T F (Nat.shiftLeft x (i0 (Nat.mod x 9))) (Nat.shiftLeft p (i0 (Nat.mod x 9)))
    (Nat.add d (Nat.mul (i0 (Nat.mod x 9)) P)) acc

/-- Continue with `k` unless the search closed. -/
def bindO (o : Option (List Ent)) (k : List Ent → Option (List Ent)) : Option (List Ent) :=
  match o with
  | none => none
  | some a => k a

/-- The frontier of the child `j`: `none` if the child class is closed. -/
def ext (P Q T F j : Nat) (f : List Ent) : Option (List Ent) :=
  List.rec (motive := fun _ => List Ent → Option (List Ent))
    (fun acc => some acc)
    (fun e _ ih acc => bindO (node P Q T F (Nat.add e.1 (Nat.mul (Nat.mul 3 j) e.2.1)) e.2.1 e.2.2 acc) ih)
    f []

/-- The child `j` is closed, or its frontier passes the check `k`. -/
def child (P Q T F j : Nat) (f : List Ent) (k : List Ent → Bool) : Bool :=
  match ext P Q T F j f with
  | none => true
  | some g => k g

/-- The frontier is nonempty. -/
def nonempty (f : List Ent) : Bool :=
  match f with
  | [] => false
  | _ :: _ => true

/-- `cover P Q F Ts f`: every child of the class with frontier `f` is closed or covered, with
band `T` at the current level and `Ts` below. -/
def cover (P Q F : Nat) (Ts : List Nat) : List Ent → Bool :=
  List.rec (motive := fun _ => List Ent → Bool)
    (fun _ => false)
    (fun T _ ih f => nonempty f && child P Q T F 0 f ih && child P Q T F 1 f ih && child P Q T F 2 f ih)
    Ts

/-- Descend from the root class `r0 (mod 3)` along the digits `js`, then `cover`. -/
def desc (P Q F : Nat) (js : List Nat) : List Nat → List Ent → Bool :=
  List.rec (motive := fun _ => List Nat → List Ent → Bool)
    (fun Ts f => cover P Q F Ts f)
    (fun j _ ih Ts f =>
      List.rec (motive := fun _ => Bool) false (fun T Ts' _ => child P Q T F j f (ih Ts')) Ts)
    js

/-- The chunk for the class with first digit `r0 ∈ {1, 2}` and further digits `js`. -/
def chunk (P Q F r0 : Nat) (js Ts : List Nat) : Bool := desc P Q F js Ts [(r0, 1, 0)]

end

end Collatz.LSA
