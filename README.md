# collatz

Lean 4 + Mathlib formalization of partial results on the Collatz conjecture.

**The conjecture itself is not proved.** `Collatz.Conjecture` is stated as a `Prop`, and
this library proves reductions and partial results about it, with no `sorry` and only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No `native_decide` is used.

## Contents

| File | Content |
| --- | --- |
| `Collatz/Basic.lean` | `step`, `ReachesOne`, `Conjecture`, `Descends`, basic lemmas |
| `Collatz/Descent.lean` | `Conjecture ↔ ∀ n ≥ 2, Descends n`; even and `1 mod 4` cases |
| `Collatz/Residue.lean` | Verified symbolic descent certificates for residue classes mod `2^k` |
| `Collatz/Verify.lean` | Kernel-checked descent of every `2 ≤ n < 1024` |
| `Collatz/Main.lean` | Main reduction theorem |

## Main result

```lean
theorem conjecture_iff_survivors_descend :
    Conjecture ↔ ∀ n, 2 ^ 10 ≤ n → n % 2 ^ 10 ∈ survivors 10 → Descends n
theorem survivors_ten_length : (survivors 10).length = 64
```

So the conjecture reduces to 64 of the 1024 residue classes mod `2^10` (6.25%).
The survivor counts for `k = 0..16` match OEIS A076227.

## Build

```sh
lake exe cache get
lake build
```
