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
| `Collatz/Cycle.lean` | Constraints on nontrivial cycles |
| `Collatz/Kernel.lean` | Kernel-friendly checkers (`resCheck`, `kall`, ...) with soundness proofs |
| `Collatz/CycleBound.lean` | Cheap cycle exponent check via rational bounds on `log₂ 3` |
| `CollatzBig/` | Generated chunked verification up to `2^24` (not a default target) |

## Main result

```lean
theorem conjecture_iff_survivors_descend :
    Conjecture ↔ ∀ n, 2 ^ 10 ≤ n → n % 2 ^ 10 ∈ survivors 10 → Descends n
theorem survivors_ten_length : (survivors 10).length = 64
```

So the conjecture reduces to 64 of the 1024 residue classes mod `2^10` (6.25%).
The survivor counts for `k = 0..16` match OEIS A076227.

## Cycle constraints

For a cycle with `a` even steps and `b` odd steps (orbit `xᵢ`):

```lean
theorem cycle_identity : 2 ^ a * ∏_{odd i} xᵢ = ∏_{odd i} (3 * xᵢ + 1)
theorem three_pow_lt_two_pow : 3 ^ b < 2 ^ a
theorem two_pow_le (hm : ∀ odd i, m ≤ xᵢ) : m ^ b * 2 ^ a ≤ (3 * m + 1) ^ b
```

Combined with the verification of all `n < 1024`, any cycle not containing `1` has
at least 41 odd steps, at least 65 even steps, and length at least 106
(`odds_card_ge`, `evens_card_ge`, `cycle_length_ge`).

## Large verification (`CollatzBig`)

`scripts/gen_big.py` generates chunk theorems proved by `decide +kernel`
(`scripts/plan.c` estimates and balances the cost). The current instance proves

```lean
theorem CollatzBig.descends_below : ∀ n, 2 ≤ n → n < 16777216 → Descends n
theorem CollatzBig.cycle_length_ge (hc : IsCycle n p) (hnr : ¬ ReachesOne n) : 31733 ≤ p
```

(at least 12276 odd and 19457 even steps). It takes about 4 minutes on 32 cores:

```sh
gcc -O2 -o plan scripts/plan.c && ./plan 16 256 > plan.txt
python3 scripts/gen_big.py 16 256 1000 96 4 plan.txt
lake build CollatzBig
```

## Build

```sh
lake exe cache get
lake build
```
