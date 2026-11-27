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
| `Collatz/Defs.lean` | Mathlib-free computational definitions evaluated by the kernel |
| `Collatz/Terras.lean` | Parity vector bijection and Terras' density theorem |
| `CollatzBig/` | Generated chunked verification up to `2^32` (not a default target) |

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

## Terras' theorem (`Collatz/Terras.lean`)

With the accelerated map `T n = n / 2` or `(3n + 1) / 2`:

```lean
-- the first k parities give a bijection between residues mod 2^k and parity vectors
theorem parity_bijective (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => fun i : Fin k => decide (kstepT^[i] r % 2 = 1))
-- almost every integer descends: the exceptions have density 0
theorem almost_all_descend (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * ((range N).filter (fun n => ¬ Descends n)).card ≤ N
```

The proof counts residues by their number `s` of odd steps (`∑ a^s b^(k-s) = (a+b)^k`):
a class with `3^s < 2^k` descends for all `n ≥ 8^k`, and with `a = 7, b = 4` at most a
proportion `(121/128)^j` of the classes mod `2^(2j)` have `3^s ≥ 2^(2j)`.

## Large verification (`CollatzBig`)

`scripts/gen_big.py` generates chunk theorems proved by `decide +kernel`
(`scripts/plan.c` estimates and balances the cost). The current instance proves

```lean
theorem CollatzBig.descends_below : ∀ n, 2 ≤ n → n < 4294967296 → Descends n
theorem CollatzBig.cycle_length_ge (hc : IsCycle n p) (hnr : ¬ ReachesOne n) : 205078 ≤ p
```

(at least 79335 odd and 125743 even steps). The 6000 residue chunks (~0.5M accelerated
steps each, ~4.5 GB peak memory, 30–45 s) total roughly 65 CPU-hours; with ~28 parallel
workers it took about 2 hours. Chunk modules only import `Collatz.Defs` (no Mathlib), so
they can be compiled independently with `lean -o` on several machines:

```sh
gcc -O2 -o plan scripts/plan.c && ./plan 24 256 > plan.txt
python3 scripts/gen_big.py 24 256 1000 6000 8 plan.txt
lake build CollatzBig
```

## Build

```sh
lake exe cache get
lake build
```
