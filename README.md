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
| `Collatz/Defs.lean` | Mathlib-free definitions evaluated by the kernel (`resCheck`, `kall`, `cycCheck2`, ...) |
| `Collatz/Kernel.lean` | Soundness proofs of the kernel checkers |
| `Collatz/CycleBound.lean` | Cheap cycle exponent check via rational bounds on `log₂ 3` |
| `Collatz/Terras.lean` | Parity vector bijection and Terras' density theorem |
| `Collatz/Korec.lean` | Density form of Terras' theorem; Korec's theorem |
| `Collatz/Lagarias.lean` | The 3x+1 conjugacy map at every finite level |
| `Collatz/TwoAdic.lean` | `T` on `ℤ_[2]`; Lagarias' conjugacy map as an isometric bijection |
| `Collatz/Periodic.lean` | Periodic points of the 2-adic map: count and rationality |
| `Collatz/StoppingTime.lean` | Exact density of integers with stopping time `≤ k` |
| `Collatz/Haar.lean` | `T` on `ℤ_[2]` preserves Haar measure |
| `Collatz/Ergodic.lean` | `T` on `ℤ_[2]` is ergodic |
| `Collatz/Bernoulli.lean` | `T` on `ℤ_[2]` is isomorphic to the Bernoulli shift |
| `Collatz/LLN.lean` | Strong law of large numbers for the parities on `ℤ_[2]` |
| `Collatz/NatCycles.lean` | Integer periodic points of the 2-adic map are Collatz cycles |
| `Collatz/Crandall.lean` | `N^c ≤ 2 #{n ≤ N reaching 1}` with `c = log 2 / log 86 ≈ 0.156` |
| `Collatz/Krasikov.lean` | At least `κ N^(3/7)` integers `≤ N` reach `1` |
| `Collatz/StoppingDist.lean` | Exact count of coefficient stopping times for every `k` (`#goodSet 100`) |
| `Collatz/TerrasD.lean` | Exponential decay of the stopping time tail (Lagarias' Theorem D) |
| `Collatz/CoeffStop.lean` | Stopping time = coefficient stopping time from tables; bounded descent |
| `Collatz/LongStop.lean` | Infinitely many `n` need `≥ 3.94 log n - c` steps to reach `1` |
| `Collatz/CLT.lean` | Central limit theorem for the parities on `ℤ_[2]` |
| `Collatz/Mixing.lean` | `T` on `ℤ_[2]` is exact and strongly mixing |
| `Collatz/Bernstein.lean` | Conjecture ⟺ `3 Q(n)` is an integer for every `n ≥ 1` |
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

A positive integer among them that does not reach `1` gives a Collatz cycle whose number of
even steps is exactly `p` (`Collatz/NatCycles.lean`: `card_evens_kstepT`), so its period is at
least `65`, and at least `125743` with the 2^32 bound (`CollatzBig/Bridge.lean`). In this
accelerated convention, used e.g. by Eliahou (1993), the cycle bound below reads `125743`.

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

`Collatz/Bernoulli.lean` identifies `(ℤ_[2], μ, T)` with the Bernoulli shift: the parity
sequence `paritySeq x = fun i => (T^i x is odd)` is a measure-preserving bijection onto
`ℕ → Bool` with the product of fair coins, with a measure-preserving inverse:

```lean
theorem paritySeq_measurePreserving : MeasurePreserving paritySeq μ bernoulli
theorem paritySeq_bijective : Function.Bijective paritySeq
theorem paritySeq_T (x : ℤ_[2]) : paritySeq (T x) = fun i => paritySeq x (i + 1)
```

`Collatz/LLN.lean` applies Mathlib's strong law of large numbers to these coins: for
Haar-almost every `x`, half of the points along the orbit are odd, so the multiplier of `T^n`
decays like `(√3 / 2)^n`:

```lean
theorem odd_fraction_ae :
    ∀ᵐ x ∂μ, Tendsto (fun n => (oddCount2 n x : ℝ) / n) atTop (𝓝 (1 / 2))
theorem multiplier_rate_ae :
    ∀ᵐ x ∂μ, Tendsto (fun n => Real.log (3 ^ oddCount2 n x / 2 ^ n) / n) atTop
      (𝓝 (Real.log 3 / 2 - Real.log 2))
```

`Collatz/CLT.lean` adds the central limit theorem (Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub`, transported along `paritySeq`), and
`Collatz/Mixing.lean` shows that `T` is exact and strongly mixing:

```lean
theorem oddCount2_clt (hZ : HasLaw Z (gaussianReal 0 (1 / 4)) P') :
    TendstoInDistribution (fun n x => ((oddCount2 n x : ℝ) - n / 2) / √n) atTop Z (fun _ => μ) P'
theorem T_exact (hS : ∀ n, ∃ E, MeasurableSet E ∧ S = T^[n] ⁻¹' E) : μ S = 0 ∨ μ S = 1
theorem T_mixing (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n => μ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B))
```

`Collatz/Bernstein.lean` gives Bernstein's (1994) non-iterative 2-adic form of the conjecture:
since `3 Q 1 = -1`, an orbit reaching `1` has `3 Q n ∈ ℤ`, and conversely the integers
`3 Q (T^m n)` eventually lie in `{-3, -2, -1, 0}`, where `Q` is injective:

```lean
theorem reachesOne_iff_three_mul_Q (hn : 1 ≤ n) :
    ReachesOne n ↔ ∃ z : ℤ, (3 : ℤ_[2]) * Q (n : ℤ_[2]) = z
theorem conjecture_iff_three_mul_Q :
    Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, 3 * Q (n : ℤ_[2]) = z
```

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

`Collatz/StoppingDist.lean` computes `#goodSet k` exactly for every `k` by a recursion over the
number of odd steps (pairing `r` with `2^k + r`), checked in the kernel:

```lean
theorem goodSet_card_add (k : ℕ) : #(goodSet k) + ∑ s ∈ range (k + 1), (aliveRow k).getD s 0 = 2 ^ k
theorem goodSet_card_hundred : #(goodSet 100) = 2 ^ 100 - 302560669500543257546172187
```

`Collatz/TerrasD.lean` bounds the tail by the binary entropy of `θ = log 2 / log 3`
(Lagarias 1985, Theorem D): a residue that has not stopped after `k` steps has at least `θ k`
odd steps, and weighting residues by `θ^s (1-θ)^(k-s)` gives

```lean
theorem badSet_card_le (k : ℕ) : (#(badSet k) : ℝ) ≤ Real.exp (k * Real.binEntropy theta)
theorem density_tail_le (k : ℕ) :
    1 - #(goodSet k) / 2 ^ k ≤ Real.exp (-((Real.log 2 - Real.binEntropy theta) * k))
```

so the density of integers with stopping time `> k` is at most about `2^(-0.05 k)`
(`H(θ) / log 2 ≈ 0.94996`, and `binEntropy_theta_lt : binEntropy theta < log 2`).

With the 2^32 verification, `CollatzBig/CoeffStop.lean` proves Terras' coefficient stopping time
conjecture up to level `125742`: if `3^(s_j n) < 2^j` for some `j < 125743` then `n ≥ 2` drops
below itself within `j` steps. So for `k < 125743` the integers with stopping time `≤ k` are
exactly the residue classes of `goodSet k`, with no exceptions:

```lean
theorem CollatzBig.stops_at_coeff_stop (hn : 2 ≤ n) (hj : 1 ≤ j) (hJ : j < 125743)
    (h : 3 ^ oddCount j n < 2 ^ j) : ∃ i, 1 ≤ i ∧ i ≤ j ∧ kstepT^[i] n < n
theorem CollatzBig.stopsBy_iff_goodSet (hk : k < 125743) (hn : 2 ≤ n) :
    (∃ j ∈ Icc 1 k, kstepT^[j] n < n) ↔ n % 2 ^ k ∈ goodSet k
```

If `n` has not dropped below itself in `j` steps then `2^j n^s ≤ (3n+1)^s`, the cycle inequality,
which `cycCheck2 (2^32)` rules out for `s < 79335` when `n ≥ 2^32`. Below `2^32` the
verification bounds the stopping time by `1000`, and `cycCheck2 (2^17)` rules out `s ≤ 630`
for `n ≥ 2^17`; the `n < 2^17` are checked directly (`CollatzBig/Cst0`-`Cst3`).

## Many integers reach 1 (`Collatz/Crandall.lean`)

Going backwards from `1`, an odd `m` with `2^a m ≡ 1 (mod 3)` has the odd predecessor
`(2^a m - 1) / 3`. Working mod `9`, every odd `m` with `3 ∤ m` has two exponents `3 ≤ a ≤ 8`
whose predecessors are again prime to `3`, so the backward tree branches at every level:

```lean
theorem card_reachesOne_ge (d : ℕ) : 2 ^ d ≤ #{n ≤ 86 ^ d | ReachesOne n}
theorem card_reachesOne_ge_rpow (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.log 2 / Real.log 86) ≤ 2 * #{n ≤ N | ReachesOne n}
```

`Collatz/Krasikov.lean` uses all exponents `2 ≤ a ≤ 30` and constants for the residues mod `27`
to reach Krasikov's exponent:

```lean
theorem card_reachesOne_ge_three_sevenths : ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
    κ * (N : ℝ) ^ ((3 : ℝ) / 7) ≤ #{n ≤ N | ReachesOne n}
```

By induction on `x - m`, `C (m % 27) (x/m)^(3/7) ≤ K #{odd n ≤ x whose backward orbit hits m}`;
the step needs `∑_a C (child % 27) (3/2^a)^(3/7) ≥ C (m % 27)` for each residue mod `81`,
checked by `decide +kernel` with the constants from `scripts/krasikov_cert.py`.
(Crandall 1978 proved such a bound for some `c > 0`, Krasikov 1989 the exponent `3/7`;
Krasikov and Lagarias later reached `0.84` with computer-assisted inequalities.)

## Long trajectories (`Collatz/LongStop.lean`)

Going backwards from `4` with a potential on the residues mod `243` (Applegate-Lagarias'
method, certificate from `scripts/longstop_cert.py`, checked by `decide +kernel`), every `L` has
an `n` with total stopping time exactly `L + 2` and at least `(2L - 13)/5` odd steps:

```lean
theorem exists_long_stopping (L : ℕ) : ∃ n, kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧ 2 * L ≤ 5 * oddCount L n + 13 ∧
    3 ^ oddCount L n * n ≤ 2 ^ (L + 2)
theorem long_stopping_log (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    5 * Real.log n - 17 * Real.log 3 ≤ (5 * Real.log 2 - 2 * Real.log 3) * (L + 2 : ℕ)
```

So infinitely many `n` reach `1` only after at least `γ log n - c` steps, `γ = 1/(log 2 - (2/5) log 3)
≈ 3.94` (trivially `1/log 2 ≈ 1.44`; Applegate and Lagarias 2003 reached `6.14` with a certificate
of 350 million codewords).

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
gcc -O2 -o plan scripts/plan.c && ./plan 24 256 > plan.txt   # regenerates the chunk files
python3 scripts/gen_big.py 24 256 1000 6000 8 plan.txt        # (byte-identical to the committed ones)
lake build Collatz
scripts/distributed/run.sh WORKDIR local:8 host:24            # compile the 6008 chunks (lean -o)
scripts/distributed/watch.sh WORKDIR                          # completion, failures, dead workers, stalls
scripts/assemble_big.sh                                       # All, Bridge, and the axiom audit Audit.lean
```

The extension `CollatzBig/Ext*.lean` (`scripts/gen_ext.py`, `scripts/assemble_ext.sh`) adds the range
`256 ≤ m < 434` with a sieve over residues mod `2^20` and reaches the ceiling of the cycle method:

```lean
theorem CollatzBig.Ext.descends_below : ∀ n, 2 ≤ n → n < 7281311744 → Descends n
theorem CollatzBig.Ext.cycle_length_ge (hc : IsCycle n p) (hnr : ¬ ReachesOne n) : 492531 ≤ p
theorem CollatzBig.Ext.kstepT_period_ge ... : 301994 ≤ p            -- accelerated convention
theorem CollatzBig.Ext.stopsBy_iff_goodSet (hk : k < 301994) (hn : 2 ≤ n) : ...
```

`CollatzBig` is deliberately not a Lake target: `lake build` would recompile all chunks
(about 4.5 GB of memory each). `CollatzBig/PROVENANCE.md` records the last clean rebuild (6008 chunks from a `git archive`,
53.9 CPU-hours, assembled and axiom-audited).

## Build

```sh
lake exe cache get
lake build      # the Collatz library
lake test       # CollatzTest: axiom audit of every Collatz.* declaration, headline statements
```

`lake test` fails if any declaration depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`; CI runs both.
