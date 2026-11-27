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
| `Collatz/Korec.lean` | Density form of Terras' theorem; Korec's theorem |
| `Collatz/Lagarias.lean` | The 3x+1 conjugacy map at every finite level |
| `Collatz/TwoAdic.lean` | `T` on `ℤ_[2]`; Lagarias' conjugacy map as an isometric bijection |
| `Collatz/Periodic.lean` | Periodic points of the 2-adic map: count and rationality |
| `Collatz/StoppingTime.lean` | Exact density of integers with stopping time `≤ k` |
| `Collatz/Haar.lean` | `T` on `ℤ_[2]` preserves Haar measure |
| `Collatz/Ergodic.lean` | `T` on `ℤ_[2]` is ergodic |
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

## Korec's theorem (`Collatz/Korec.lean`)

```lean
-- the proportion of n < N that never drop below n tends to 0
theorem density_not_descends :
    Tendsto (fun N => ((range N).filter (fun n => ¬ Descends n)).card / (N : ℝ)) atTop (𝓝 0)
-- Korec (1994): for c > log 3 / log 4 ≈ 0.7925, almost every n reaches a value below n ^ c
theorem korec {c : ℝ} (hc : Real.log 3 / Real.log 4 < c) (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * ((range N).filter (fun n => ∀ j, (n : ℝ) ^ c ≤ step^[j] n)).card ≤ N
```

For `2^t ≤ n < 2^(t+1)` with `s` odd steps among the first `t`, `T^t n < 2·3^s + (3/2)^t`.
The second moment `∑_{r < 2^t} (2 s(r) - t)^2 = t 2^t` shows that `s ≤ t (1 + 1/L) / 2` for
all but `L^2 2^t / t` of these `n`, and then `T^t n < n ^ c` for large `t`.

## The conjugacy map (`Collatz/Lagarias.lean`)

`parityVec k n = ∑_{i < k} (T^i n mod 2) 2^i` is the level-`k` truncation of Lagarias'
conjugacy map `Q_∞ : ℤ₂ → ℤ₂`:

```lean
theorem parityVec_eq_iff (k n n' : ℕ) : parityVec k n = parityVec k n' ↔ n % 2 ^ k = n' % 2 ^ k
theorem parityVec_bijective (k : ℕ) : Function.Bijective (fun r : Fin (2 ^ k) => ⟨parityVec k r, _⟩)
theorem parityVec_compat (k n : ℕ) : parityVec (k + 1) n % 2 ^ k = parityVec k n
theorem parityVec_kstepT (k n : ℕ) : parityVec k (kstepT n) = parityVec (k + 1) n / 2
```

`Collatz/TwoAdic.lean` builds the 2-adic version: `T x = (x + par x * (2x + 1)) / 2` on
`ℤ_[2]` (extending `kstepT`, `T_natCast`) and `Q x = ∑' i, par (T^[i] x) * 2^i`:

```lean
noncomputable def Qequiv : ℤ_[2] ≃ᵢ ℤ_[2]       -- Q is an isometric bijection
theorem Qequiv_conj (x : ℤ_[2]) : Qequiv (T x) = shift (Qequiv x)
```

so `T` on `ℤ₂` is conjugate to the shift `y ↦ (y - par y) / 2`.
`Collatz/Periodic.lean` uses this to describe all periodic points:

```lean
theorem card_periodic {p : ℕ} (hp : 1 ≤ p) : Nat.card {x : ℤ_[2] // T^[p] x = x} = 2 ^ p
theorem periodic_rational {p : ℕ} (hp : 1 ≤ p) {x : ℤ_[2]} (hx : T^[p] x = x) :
    ∃ a b : ℤ, Odd b ∧ (b : ℤ_[2]) * x = a
```

`Collatz/Haar.lean` equips `ℤ_[2]` with its Haar probability measure `μ`
(`μ (closedBall a (2^-k)) = 2^-k`) and shows that `T` preserves it:

```lean
theorem T_measurePreserving : MeasurePreserving T μ μ
```

The balls form a π-system generating the Borel σ-algebra; isometric bijections such as `Q`
map balls to balls, the shift pulls a ball back to two balls of half the radius, and
`T = Q⁻¹ ∘ shift ∘ Q`.

`Collatz/Ergodic.lean` shows that `T` is ergodic:

```lean
theorem T_ergodic : Ergodic T μ
```

For a ball `B` of radius `2^-k` and measurable `E`, `μ (B ∩ shift^[k] ⁻¹' E) = 2^-k μ E`; so a
shift-invariant `S` satisfies `μ.restrict S = μ S • μ`, hence `μ S = μ S ^ 2`.

## Stopping times (`Collatz/StoppingTime.lean`)

The integers with stopping time `≤ k` (`T^j n < n` for some `1 ≤ j ≤ k`) have natural density
exactly `#(goodSet k) / 2^k`, where `goodSet k` is the set of residues mod `2^k` with
coefficient stopping time `≤ k` (`3^(s_j r) < 2^j` for some `1 ≤ j ≤ k`):

```lean
theorem density_stopsBy (k : ℕ) : Tendsto
    (fun N => #{n ∈ range N | ∃ j ∈ Icc 1 k, kstepT^[j] n < n} / (N : ℝ)) atTop
    (𝓝 (#(goodSet k) / 2 ^ k))
theorem goodSet_card_four : (goodSet 4).card = 13   -- densities 1/2, 3/4, 3/4, 13/16, ...
```

The two notions agree for every `n ≥ 3^k` (`stopsBy_imp`, `imp_stopsBy`).

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

`scripts/distributed/` compiles the chunk modules in parallel on several machines over ssh
(`run.sh WORKDIR local:8 host:24`), with `watch.sh` reporting completion, failures, dead
workers and stalls.

## Build

```sh
lake exe cache get
lake build
```
