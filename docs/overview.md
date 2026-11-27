# Partial results on the Collatz conjecture, formalized in Lean 4

*An overview of the `collatz-conjecture-lean` development.*

## Abstract

We describe a Lean 4 + Mathlib formalization of a broad selection of partial results on the
Collatz (3x+1) problem. It contains (i) kernel-checked verifications that every
`2 ≤ n < 7 281 311 744` drops below itself, and the resulting lower bound `492 531` on the length
of a nontrivial cycle; (ii) Baker-free, bounded forms of Steiner's theorem on 1-cycles (no
nontrivial circuit with fewer than `6 586 818 670` odd steps) and of Simons–de Weger's theorem on
`m`-cycles (up to `m = 469`); (iii) the density theorems of Terras, Everett and Korec, the exact
distribution of stopping times and Lagarias' exponential tail bound, and Terras' coefficient
stopping time conjecture up to level `301 993`; (iv) lower bounds for the number of integers
reaching 1 (Crandall, Krasikov's exponent `3/7`) and for the length of convergent trajectories
(Applegate–Lagarias' method); and (v) the 2-adic theory of the map: Lagarias' conjugacy as an
isometric bijection of `ℤ₂`, periodic points, Haar measure preservation, exactness, strong mixing,
the Bernoulli isomorphism, the strong law, the central limit theorem, equidistribution, and
Lagarias' 2-adic form of the conjecture (`3Q(n) ∈ ℤ`). The conjecture itself is not proved. All
1184 constants of the `Collatz` library (including auxiliary ones) and all `CollatzBig` headline
theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry` and no `native_decide`.

## 1. Introduction

The Collatz map sends `n` to `n/2` if `n` is even and to `3n+1` if `n` is odd; the conjecture
states that every positive integer eventually reaches 1. It remains open. A large literature
proves partial results: density statements, constraints on hypothetical cycles, lower bounds on
the set of integers that reach 1, and a detailed theory of the map's 2-adic extension
[Lagarias 1985, Wirsching 1998]. Computations have verified the conjecture far beyond the range
treated here.

This development formalizes a representative core of that literature in a single Lean library.
Its distinctive features are:

- **Kernel-checked computation without `native_decide`.** Large finite checks are written as
  `Nat.rec`/`Bool` functions with soundness proofs and evaluated by `decide +kernel`, which uses
  the kernel's GMP-backed `Nat` arithmetic. Nothing is trusted beyond the Lean kernel.
- **Mechanical trust checks.** `lake test` collects the axioms of every declaration of the `Collatz`
  library and fails on anything other than `propext`, `Classical.choice` and `Quot.sound`; a second
  test file restates the main `Collatz.*` theorems. The large verifications carry their own
  `#guard_msgs` axiom audits.
- **Reproducible provenance.** The 10 263 residue and cycle chunks of the large verification were
  rebuilt from `git archive` (of two commits with byte-identical chunk sources) on our machines;
  hashes, timings and the assembly are recorded in `CollatzBig/PROVENANCE.md`. A GitHub Actions
  workflow (`big.yml`) recompiles all 10 267 chunks from source and reruns the assembly and audits.
- **Baker-free cycle results.** Mathlib has no theory of linear forms in logarithms. We replace
  Baker-type bounds by explicit Farey pairs for `log₂ 3` certified in the kernel, combined with
  the verified range. This yields bounded versions of results that are proved in the literature
  with Baker's theorem.

### Provenance of this work

The library was written in one day (2026-11-27) by an AI assistant (Claude) working with the
repository owner, with distributed computation on the owner's machines. All statements were
checked by the Lean kernel, and the repository was reviewed by independent automated passes
(statement audit, adversarial checks of claims). Section 9 lists what is not covered.

## 2. Setting and conventions

- `step n` is the Collatz map, `ReachesOne n := ∃ k, step^[k] n = 1`,
  `Conjecture := ∀ n ≥ 1, ReachesOne n`, and `Descends n := ∃ k ≥ 1, step^[k] n < n`.
- The accelerated map is `T n = kstepT n = n/2` (even) or `(3n+1)/2` (odd);
  `s_j(n) = oddCount j n` counts the odd values among `n, T n, …, T^(j-1) n`.
- `ReachesOne n ↔ ∃ j, kstepT^[j] n = 1` (`reachesOne_iff_exists_kstepT`), and
  `Conjecture ↔ ∀ n ≥ 2, Descends n` (`conjecture_iff_descends`).
- Cycle lengths are counted in `step` units (`IsCycle n p`); the literature often counts
  `T`-steps, which equals the number of even steps (`card_evens_kstepT`). We give both.

## 3. Finite verification

### 3.1 Residue certificates

Write `n = 2^k m + r`. While the coefficient of `m` is even, the parity of `a m + b` is that of
`b`, so the orbit of the whole class is an affine function of `m` (`step_affine`). `cert k r`
runs this symbolically; once the form is `a' m + b'` with `a' < 2^k` and `b' ≤ r`, every
`n ≥ 2^k` in the class descends (`descends_of_cert`). Mod `2^10`, 64 classes survive, so the
conjecture is equivalent to descent in those classes (`conjecture_iff_survivors_descend`).

### 3.2 Chunked kernel checks

`resCheck k M fuel r` either certifies `r` and checks `r` itself, or checks every
`n = 2^k m + r` with `m < M` by iterating `kstepT` up to `fuel` times. The range `n < 2^32` uses
`k = 24`, `M = 256`, `fuel = 1000`: the `2^24` residues are split into 6000 cost-balanced chunks
(about `5·10^5` accelerated steps each), each a theorem
`kallFrom (resCheck 24 256 1000) lo len = true := by decide +kernel`. A C mirror (`plan.c`)
estimates the cost of every residue (286 581 survivors mod `2^24`, `3.0·10^9` steps in total,
at most 447 steps per number). The chunks are combined by a balanced tree of explicitly typed
`kallFrom_append` theorems.

The extension to `434·2^24` adds `256 ≤ m < 434` without touching the existing chunks. A sieve
walks each residue mod `2^20` down four levels, trying `cert` at every node, so only the 286 581
survivors mod `2^24` are checked directly (4235 chunks, 32 million `certAux` iterations instead of
81 million for a flat design).

Chunk modules import only a Mathlib-free definitions file, so they load quickly and compile
independently with `lean -o` on several machines (`scripts/distributed/`). Kernel memory grows
with the work in one declaration (roughly 9 GB per million steps, as observed in our runs), which fixes the chunk size;
each chunk takes 30–45 s and about 4.5 GB.

### 3.3 Provenance

The chunks were recompiled from `git archive`: 6008 chunks for `2^32` from commit `8878d4d` (53.9 CPU
hours on two machines) and 4255 for the extension from commit `49a126a`, whose chunk sources are
byte-identical (about 38 hours on three machines), all
successful; infrastructure failures (a missing dependency on one host, two ssh resets) were
requeued and recorded. The assembly then compiled the combining modules and the axiom audits.
The source and build-product hashes are in `CollatzBig/PROVENANCE.md`.

## 4. Cycles

### 4.1 Length of a nontrivial cycle

For a cycle with `a` even and `b` odd steps, `2^a ∏ xᵢ = ∏ (3xᵢ + 1)` over its odd elements, so
`3^b < 2^a`, and `m^b 2^a ≤ (3m+1)^b` if all odd elements are `≥ m`. Taking logarithms,
`b log₂ 3 < a ≤ b log₂ 3 + b/(3m ln 2)`. `cycCheck2 N b` refutes this pair using only the
convergents `176251/111202 < log₂ 3 < 301994/190537` and `log 2 > 0.6931471803`, so it is cheap
for every `b` (`Collatz/CycleBound.lean`). With the verified range `N = 434·2^24`, a nontrivial
cycle has at least 190 537 odd and 301 994 even steps, hence length `≥ 492 531`
(`CollatzBig.Ext.cycle_length_ge`). The threshold `N ≥ 7 269 381 033` where the bound jumps from
79 335 to 190 537 odd steps was located exactly; since `190537` is the convergent's denominator,
no larger verified range improves this method.

### 4.2 Circuits (1-cycles)

A circuit (`k` odd steps followed by `l` even steps) satisfies `2^(k+l) n + 2^k = 3^k n + 3^k`,
so `0 < (k+l) - k log₂ 3 < 1/(n ln 2)`. If `a/b < log₂ 3 < c/d` are adjacent Farey fractions
(`bc - ad = 1`), every fraction strictly between them has denominator `≥ b + d`, and the remaining
lattice points `s(c,d) - t(a,b)` are excluded by size; the single critical point `(K,k) = (c,d)`
is excluded because the resulting `n` is not an integer. With `n ≥ 7 281 311 744` and the pair
`9809721694/6189245291 < log₂ 3 < 630138897/397573379`, every circuit with
`k < 6 586 818 670` is `1 → 2 → 1` (`CollatzBig.Circuit.no_circuit`). Steiner [1978] excluded all
nontrivial circuits using Baker's theorem.

### 4.3 Cycles with few odd blocks

For a cycle of length `K` with `k` odd steps, `m` maximal odd blocks and all elements `≥ N`, a
product identity in which only block starts contribute gives `N^m 2^K ≤ (N+1)^m 3^k`, i.e.
`0 < K ln 2 - k ln 3 ≤ m ln(1 + 1/N)`. A Farey pair whose gap exceeds `m ln(1+1/N)` excludes all
lattice points, which gives (`CollatzBig.MCycle`):

| odd blocks `m ≤` | 13 | 38 | 63 | 68 | 88 | 469 |
| --- | --- | --- | --- | --- | --- | --- |
| no nontrivial cycle with fewer odd steps than | 397 573 379 | 171 928 773 | 118 212 940 | 64 497 107 | 64 497 107 | 10 781 274 |

Simons and de Weger [2005] excluded all cycles with `m ≤ 68` using Baker's theorem. For `m ≥ 2`
there is no closed form for `n`, so the integrality step of 4.2 does not transfer.

### 4.4 Integer periodic points

A positive integer with `T^p n = n` that does not reach 1 is a Collatz cycle with exactly `p`
even steps, so `p ≥ 301 994` (`CollatzBig.Ext.kstepT_period_ge`).

## 5. Density and stopping times

- **Terras–Everett.** The first `k` parities give a bijection between residues mod `2^k` and
  parity vectors (`parity_bijective`). Counting residues by the number `s` of odd steps,
  `∑ a^s b^(k-s) = (a+b)^k`, shows that the classes with `3^s ≥ 2^k` are a vanishing proportion;
  a class with `3^s < 2^k` descends for all `n ≥ 8^k`. Hence the exceptions to descent have
  density 0 (`almost_all_descend`, `density_not_descends`).
- **Exact distribution.** The integers with stopping time `≤ k` have density exactly
  `#goodSet k / 2^k` (`density_stopsBy`), where `goodSet k` consists of the residues whose
  coefficient `3^(s_j)/2^j` drops below 1 by step `k`. `#goodSet k` is computed for every `k` by a
  recursion over `s` evaluated in the kernel; e.g. `#goodSet 100 = 2^100 - 302560669500543257546172187`.
- **Theorem D.** Weighting residues by `θ^s (1-θ)^(k-s)` with `θ = log 2 / log 3` gives
  `#badSet k ≤ exp(k H(θ))`, `H` the binary entropy, so the density of stopping time `> k` is at
  most about `2^(-0.05 k)` (`density_tail_le`) [Lagarias 1985].
- **Coefficient stopping time conjecture** [Terras 1976]. If `n` has not dropped below itself
  within `j` steps then `2^j n^s ≤ (3n+1)^s` (`pow_two_le_of_no_descent`), the cycle inequality.
  It is refuted by `cycCheck2` for `n` above the verified range; below it, the verification bounds
  the stopping time by 1000, and `cycCheck2 (2^17)` handles `2^17 ≤ n`; smaller `n` are checked
  directly. Therefore, for `k < 301 994`, the `n ≥ 2` with stopping time `≤ k` are exactly the
  classes of `goodSet k` (`CollatzBig.Ext.stopsBy_iff_goodSet`).
- **Korec.** For `c > log 3 / log 4`, almost every `n` reaches a value below `n^c` (`korec`),
  via `T^t n < 2·3^s + (3/2)^t` for `2^t ≤ n < 2^(t+1)` and the second moment
  `∑_r (2 s(r) - t)^2 = t 2^t`.

## 6. Integers reaching 1 and long trajectories

- **Crandall-type bound.** Backwards from 1, every odd `m` prime to 3 has two exponents
  `3 ≤ a ≤ 8` whose predecessors `(2^a m - 1)/3` are again prime to 3; parent recovery from
  `3k + 1 = 2^a m` makes the tree injective, so at least `N^c / 2` integers `≤ N` reach 1, `c = log 2 / log 86 ≈ 0.1556` (`card_reachesOne_ge_rpow`; Crandall [1978] proved some `c > 0`).
- **Krasikov's exponent 3/7.** With all exponents `2 ≤ a ≤ 30` and constants `C_r` for the
  residues mod 27, induction on `x - m` gives `C_{m mod 27} (x/m)^{3/7} ≤ K · #(backward tree of
  m below x)`. The step needs one inequality per residue mod 81, checked by `decide +kernel` after
  replacing `(3/2^a)^{3/7}` by rational lower bounds verified through seventh powers. In exploratory
  computations (not in the repository), constants mod `3^h` gave exponents of about 0.436, 0.450,
  0.460, 0.470 for `h = 3..6`; the
  Krasikov–Lagarias exponent 0.84 needs a different, much larger system.
- **Long trajectories** [Applegate–Lagarias 2003]. A potential `h` on the residues mod 243 with
  `h(a) + 2 ≤ h(a') + 5·[odd move]` for some backward move from every residue mod 729
  prime to 3 gives, for
  every `L`, an `n` with total stopping time exactly `L + 2` and at least `(2L - 13)/5` odd steps,
  hence `σ(n) ≥ 3.94 log n - c` for infinitely many `n` (`long_stopping_log`). The published
  constant is 6.14316, with a certificate of about 350 million codewords (trees of depth ≤ 60).

## 7. The 2-adic map

`T` extends to `ℤ₂` by `T x = (x + par x (2x+1))/2`, and `Q x = ∑ par(T^i x) 2^i` reads the
parity sequence as a 2-adic integer.

- `2^k ∣ Q x - Q y ↔ 2^k ∣ x - y`, the range of `Q` is closed and dense, and `Q ∘ T = shift ∘ Q`:
  `Q` is an isometric bijection conjugating `T` to the shift (`Qequiv`, `Qequiv_conj`).
  Lagarias [1985, Thm L] states that `Q` is a measure-preserving homeomorphism (observed earlier by
  Terras and Pomerance); the isometry and an explicit inverse are in Bernstein–Lagarias [1996]. The finite levels (`parityVec`) are permutations of the residues mod `2^k`.
- Periodic points of the shift are `a/(1-2^p)`, so `ℤ₂` has exactly `2^p` points with
  `T^p x = x`, each rational with odd denominator (`card_periodic`, `periodic_rational`); rationality of
  the periodic points also follows from Bernstein's formula for `Q⁻¹` [1994].
- Haar measure on `ℤ₂` is constructed with `μ(closedBall a 2^-k) = 2^-k`; balls form a π-system
  generating the Borel σ-algebra. Isometric bijections and the shift preserve `μ`, hence so does
  `T`. The identity `μ(B ∩ shift^-k E) = 2^-k μ(E)` for balls `B` of radius `2^-k` gives
  ergodicity, exactness and, with approximation by cylinder sets, strong mixing. Measure
  preservation and strong mixing are due to Matthews–Watts [1984] (Lagarias [1985], Thm K).
- The parity sequence is a measure-preserving bijection onto the Bernoulli(1/2) product measure
  (so `T` is Bernoulli; cf. Lagarias [1985, Thm L], Bernstein–Lagarias [1996]). Mathlib's strong law and central limit theorem then give `s_n/n → 1/2` almost surely and
  `(s_n - n/2)/√n → N(0, 1/4)`; a block strong law over disjoint windows gives equidistribution of
  almost every orbit mod `2^k` for every `k` (Matthews–Watts [1984]; Lagarias [1985, Thm K]).
  The strong law and the CLT are immediate from the Bernoulli property; we know no specific source.
- **The 2-adic form of the conjecture.** Since `3 Q 1 = -1`, `ReachesOne n ↔ 3 Q(n) ∈ ℤ` for
  `n ≥ 1`, so the conjecture is equivalent to `3 Q(n) ∈ ℤ` for every positive integer
  (`conjecture_iff_three_mul_Q`). This is Lagarias' third form of the conjecture [1985, §2.8];
  Bernstein [1994] gave an explicit non-iterative formula for `Φ = Q⁻¹` and the equivalent statement
  `ℤ⁺ ⊆ Φ(⅓ℤ)`, which we do not formalize.

## 8. Engineering notes

- **`decide +kernel` at scale.** The kernel evaluates `Nat` literals with GMP, so `Nat.rec` loops
  over hundreds of thousands of steps are feasible; memory grows with the work in one declaration.
  Combining thousands of chunk theorems by a linear chain of `have`s is super-linear (the types
  accumulate unevaluated sums); a balanced tree of explicitly typed theorems takes seconds.
- **Functions the kernel does not accelerate.** Evaluating `Nat.log2 (3^79335)` with
  `decide +kernel` did not finish; the bound was derived by `omega` from the convergent inequality.
- **Kernel numeral limits.** A single numeral is limited to `2^30` bits (128 MB), and `Nat.pow`
  is rejected when the predicted result is too large; exponents are therefore split as
  `(3^1048576)^q · 3^r`. Defeq checks between closed terms containing an unsplit huge power
  (core `instPowNat` against Mathlib's `Monoid.npow`) make the kernel attempt the full power, so
  certificates are stated with the power function abstracted.
- **Build tooling.** Modules compiled with `lean -o` have no Lake traces, so `lake build` would
  recompile them; the large verification is therefore outside the Lake graph and assembled by
  scripts. Lake's local artifact cache and remote `lake cache` exist but were not needed.

## 9. Limitations and outlook

- Nothing here proves the conjecture or excludes all cycles. The cycle results are bounded; the
  unbounded versions in the literature use Baker's theorem, which is not in Mathlib.
- The verified range (`7.3·10^9`) is far below published computations; it was chosen as the point
  where the cycle method saturates.
- Not formalized: Tao's theorem that almost all orbits attain almost bounded values, the
  Krasikov–Lagarias exponent 0.84, Applegate–Lagarias' constant 6.14, and the full Steiner and
  Simons–de Weger theorems.
- Natural extensions are larger certificates for the long-trajectory constant and the Krasikov
  exponent, and an integrality argument for `m ≥ 2` in 4.3.

## References

- D. Applegate, J. C. Lagarias, *Lower bounds for the total stopping time of 3x+1 iterates*,
  Math. Comp. 72 (2003), 1035–1049.
- D. J. Bernstein, *A non-iterative 2-adic statement of the 3N+1 conjecture*, Proc. AMS 121 (1994), 405–408.
- D. J. Bernstein, J. C. Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math. 48 (1996), 1154–1169.
- R. E. Crandall, *On the "3x+1" problem*, Math. Comp. 32 (1978), 1281–1292.
- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- C. J. Everett, *Iteration of the number-theoretic function f(2n) = n, f(2n+1) = 3n+2*,
  Adv. Math. 25 (1977), 42–45.
- I. Korec, *A density estimate for the 3x+1 problem*, Math. Slovaca 44 (1994), 85–89.
- I. Krasikov, *How many numbers satisfy the 3x+1 conjecture?*, Internat. J. Math. Math. Sci. 12
  (1989), 791–796.
- I. Krasikov, J. C. Lagarias, *Bounds for the 3x+1 problem using difference inequalities*,
  Acta Arith. 109 (2003), 237–258.
- J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92 (1985), 3–23.
- K. R. Matthews, A. M. Watts, *A generalization of Hasse's generalization of the Syracuse
  algorithm*, Acta Arith. 43 (1984), 167–175.
- J. Simons, B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*,
  Acta Arith. 117 (2005), 51–70.
- R. P. Steiner, *A theorem on the Syracuse problem*, Proc. 7th Manitoba Conf. Numer. Math. Comput. (Winnipeg, 1977),
  Congr. Numer. 20 (1978), 553–559.
- T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*, Forum Math. Pi 10
  (2022), e12.
- R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976), 241–252.
- G. J. Wirsching, *The Dynamical System Generated by the 3n+1 Function*, LNM 1681, Springer (1998).

## Appendix: size of the development

| Part | Size |
| --- | --- |
| Library `Collatz/` (35 files) | 5 873 lines, 1 184 constants (including auxiliary ones) |
| Tests `CollatzTest/` | 148 lines |
| Generated chunks `CollatzBig/` | 10 267 chunk modules (about 2 MB of source), assemblies of 24 077 and 17 124 lines |
| Kernel certificates | numerals of up to 630 million bits (circuit), 270 million (m-cycles) |
| Computation | about 92 hours of compute for the clean rebuild on our machines |
