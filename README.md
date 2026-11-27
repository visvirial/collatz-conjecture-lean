# collatz-conjecture-lean

A Lean 4 + Mathlib formalization of partial results on the Collatz (3x+1) conjecture.

**The conjecture itself is not proved.** `Collatz.Conjecture` is stated as a `Prop`. The library
proves reductions, density theorems, cycle constraints, kernel-checked verifications and the
2-adic theory of the map. There is no `sorry`, no `native_decide`, and every declaration depends
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound` (checked by `lake test`
for the `Collatz` library and by `#guard_msgs` audits for `CollatzBig`).

Notation: `step n = n/2` or `3n+1`; the accelerated map `T n = kstepT n = n/2` or `(3n+1)/2`;
`s_j(n)` (`oddCount j n`) is the number of odd values among `n, T n, …, T^(j-1) n`.

## Results at a glance

| Result | Lean | Literature |
| --- | --- | --- |
| Every `2 ≤ n < 7281311744` (`= 434·2^24`) drops below itself, hence reaches 1 | `CollatzBig.Ext.descends_below` | (verification) |
| A nontrivial cycle has length `≥ 492531` (`≥ 301994` in the accelerated convention) | `CollatzBig.Ext.cycle_length_ge` | cf. Eliahou 1993 |
| No nontrivial circuit (1-cycle) with fewer than `6586818670` odd steps, without Baker | `CollatzBig.Circuit.no_circuit` | Steiner 1978 (bounded form) |
| No nontrivial cycle with `≤ 68` odd blocks and fewer than `64497107` odd steps (up to 469 blocks with smaller bounds) | `CollatzBig.MCycle.reachesOne_of_blocks_le_68` | Simons–de Weger 2005 (bounded form) |
| Conjecture ⟺ descent in 64 of the 1024 classes mod `2^10` | `conjecture_iff_survivors_descend` | cf. Terras 1976 (classes mod `2^k`) |
| Almost every `n` drops below itself (density 0 of exceptions) | `almost_all_descend`, `density_not_descends` | Terras 1976, Everett 1977 |
| Exact density of stopping time `≤ k`, exponential tail `≈ 2^(-0.05k)` | `density_stopsBy`, `density_tail_le` | Terras 1976, Lagarias 1985 (Thm D) |
| Coefficient stopping time conjecture up to level `301993` | `CollatzBig.Ext.stopsBy_iff_goodSet` | Terras 1976 |
| Almost every `n` gets below `n^c` for every `c > log 3 / log 4` | `korec` | Korec 1994 |
| At least `κ N^0.4848` integers `≤ N` reach 1 | `card_reachesOne_ge_rpow_krasikov` | Crandall 1978, Krasikov 1989 (method) |
| Infinitely many `n` need `≥ 5.38 log n - c` steps to reach 1 | `long_stopping_log_twelve` | Applegate–Lagarias 2003 (method) |
| `T` on `ℤ₂` is conjugate to the shift by an isometric bijection `Q` | `TwoAdic.Qequiv`, `Qequiv_conj` | Lagarias 1985 (Thm L), Bernstein–Lagarias 1996 |
| `ℤ₂` has exactly `2^p` points of period dividing `p`, all rational | `TwoAdic.card_periodic`, `periodic_rational` | cf. Lagarias 1985, Bernstein 1994 |
| `T` preserves Haar measure, is exact, strongly mixing and Bernoulli | `T_measurePreserving`, `T_exact`, `T_mixing`, `paritySeq_measurePreserving` | Matthews–Watts 1984, Lagarias 1985 (Thms K, L), Bernstein–Lagarias 1996 |
| Law of large numbers, central limit theorem and equidistribution mod `2^k` for 2-adic orbits | `odd_fraction_ae`, `oddCount2_clt`, `orbit_equidistributed_mod` | equidistribution: Matthews–Watts 1984, Lagarias 1985 (Thm K); LLN and CLT follow from the Bernoulli property |
| Conjecture ⟺ `3 Q(n) ∈ ℤ` for every `n ≥ 1` | `TwoAdic.conjecture_iff_three_mul_Q` | Lagarias 1985 (third form); Bernstein 1994 (via an explicit `Q⁻¹`) |

A longer write-up (methods, engineering notes, references) is in [`docs/overview.md`](docs/overview.md).

The `CollatzBig.*` results rest on 10267 kernel-checked chunk theorems and two certificate modules;
see [`CollatzBig/PROVENANCE.md`](CollatzBig/PROVENANCE.md) for the clean rebuild from `git archive`,
and `.github/workflows/big.yml` for a re-verification of all of them from source on GitHub Actions.

## Building and checking

```sh
lake exe cache get
lake build      # the Collatz library (CI)
lake test       # CollatzTest: axiom audit of every Collatz.* declaration, and the main statements
```

`CollatzTest/Axioms.lean` fails the build if any `Collatz.*` declaration uses an axiom other than
`propext`, `Classical.choice`, `Quot.sound`; `CollatzTest/Statements.lean` restates the main
`Collatz.*` theorems (the `CollatzBig` ones are outside the Lake build). Both run in CI.

The large verifications (`CollatzBig/`) are not a Lake target, because `lake build` would recompile
every chunk (about 4.5 GB of memory and 40 s each). They are compiled with `lean -o` and assembled
by scripts; `CollatzBig/Audit.lean`, `ExtAudit.lean`, `CircuitAudit.lean` and `MCycleAudit.lean` check their axioms with
`#guard_msgs`. See [Large verification](#large-verification-collatzbig).

## Results in detail

### Reduction and residue certificates

```lean
theorem conjecture_iff_survivors_descend :
    Conjecture ↔ ∀ n, 2 ^ 10 ≤ n → n % 2 ^ 10 ∈ survivors 10 → Descends n
theorem survivors_ten_length : (survivors 10).length = 64
```

`cert k r` tracks the orbit of `2^k m + r` as an affine form in `m`; a class is certified once the
coefficient drops below `2^k` (`Collatz/Residue.lean`). The survivor counts for `k = 0..16` agree
with OEIS A076227 (checked numerically; only `k = 10` is a theorem).

### Cycles

For a cycle with `a` even and `b` odd steps (orbit `xᵢ`), `2^a ∏ xᵢ = ∏ (3xᵢ + 1)` over the odd
`xᵢ`, so `3^b < 2^a` and `m^b 2^a ≤ (3m+1)^b` when all odd elements are `≥ m`
(`Collatz/Cycle.lean`). With the verification below `1024`, a direct exponent check gives cycle
length `≥ 106` (`noCycleExponents_1024`). `cycCheck2` (`Collatz/CycleBound.lean`) refutes the
inequalities with the convergents `176251/111202 < log₂ 3 < 301994/190537` and small integers only;
with `7281311744` it gives length `≥ 492531` (odd `≥ 190537`, even `≥ 301994`), which is the
ceiling of this method.

A positive integer periodic point of the 2-adic map with period `p` that does not reach 1 is a Collatz cycle with exactly `p`
even steps (`Collatz/NatCycles.lean`: `card_evens_kstepT`), so `p ≥ 65`, and `p ≥ 301994` with the
large verification.

A circuit (`k` odd steps, then `l` even steps, back to `n`) satisfies
`2^(k+l) n + 2^k = 3^k n + 3^k`, so `(k+l)/k` approximates `log₂ 3` within `1/(k n ln 2)`. With
`n ≥ 7281311744` and the adjacent Farey fractions
`9809721694/6189245291 < log₂ 3 < 630138897/397573379` (from kernel certificates with numerals of
up to 630 million bits in `CollatzBig/CircuitCert.lean`, combined in `CollatzBig/Circuit.lean`), every circuit with `k < 6586818670` is the
trivial one (`Collatz/Circuit.lean`, `CollatzBig/Circuit.lean`):

```lean
theorem CollatzBig.Circuit.no_circuit {n k l : ℕ} (hc : IsCircuit n k l) (hk : k < 6586818670) :
    n = 1 ∧ k = 1 ∧ l = 1
```

More generally (`Collatz/MCycle.lean`, `CollatzBig/MCycle.lean`), a `T`-cycle of length `K` with
`k` odd steps, `m` odd blocks and all elements `≥ N` satisfies `N^m 2^K ≤ (N+1)^m 3^k` (only block
starts contribute), so `0 < K ln 2 - k ln 3 ≤ m ln(1 + 1/N)`. One Farey pair per range of `m` then
excludes all lattice points (`scripts/mcycle_cert.py`, certificates in `CollatzBig/MCycleCert.lean`
and `CircuitCert.lean`):

| odd blocks `m ≤` | 13 | 38 | 63 | 68 | 88 | 469 |
| --- | --- | --- | --- | --- | --- | --- |
| no nontrivial cycle with odd steps `<` | 397573379 | 171928773 | 118212940 | 64497107 | 64497107 | 10781274 |

```lean
theorem CollatzBig.MCycle.reachesOne_of_blocks_le_68 (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hper : kstepT^[K] n = n) (hm : oddBlocks K n ≤ 68) (hk : oddCount K n < 64497107) : ReachesOne n
```

(Simons and de Weger excluded all `m ≤ 68` with Baker's theorem; for `m = 1` the integrality of
the circuit equation gives the larger bound above, which does not carry over to `m ≥ 2`.)

### Density and stopping times

```lean
-- Terras: parity vectors of length k correspond to residues mod 2^k
theorem parity_bijective (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => fun i : Fin k => decide (kstepT^[i] r % 2 = 1))
-- the exceptions to descent have density 0
theorem density_not_descends :
    Tendsto (fun N => #{n < N | ¬ Descends n} / N) atTop (𝓝 0)
-- exact density of stopping time ≤ k, and its exponential tail
theorem density_stopsBy (k : ℕ) :
    Tendsto (fun N => #{n < N | ∃ j ∈ Icc 1 k, kstepT^[j] n < n} / N) atTop (𝓝 (#(goodSet k) / 2 ^ k))
theorem density_tail_le (k : ℕ) :
    1 - #(goodSet k) / 2 ^ k ≤ Real.exp (-((Real.log 2 - Real.binEntropy theta) * k))
theorem goodSet_card_hundred : #(goodSet 100) = 2 ^ 100 - 302560669500543257546172187
-- Korec: almost every n gets below n^c
theorem korec {c : ℝ} (hc : Real.log 3 / Real.log 4 < c) (q : ℕ) : ∃ N0, ∀ N ≥ N0,
    q * #{n < N | ∀ j, n ^ c ≤ step^[j] n} ≤ N
```

- Terras (`Collatz/Terras.lean`): residues are counted by their number of odd steps
  (`∑ a^s b^(k-s) = (a+b)^k`); a class with `3^s < 2^k` descends for all `n ≥ 8^k`.
- Korec (`Collatz/Korec.lean`): for `2^t ≤ n < 2^(t+1)`, `T^t n < 2·3^s + (3/2)^t`, and the second
  moment `∑_r (2 s(r) - t)^2 = t 2^t` controls `s`.
- `Collatz/StoppingTime.lean`: stopping time and coefficient stopping time agree for `n ≥ 3^k`.
- `Collatz/StoppingDist.lean`: `#goodSet k` for every `k` by a recursion over `s`, evaluated in
  the kernel.
- `Collatz/TerrasD.lean`: weighting residues by `θ^s (1-θ)^(k-s)` with `θ = log 2 / log 3` gives
  `#badSet k ≤ exp (k H(θ))`, where `H(θ) / log 2 ≈ 0.94996` (Lagarias 1985, Theorem D).
- Coefficient stopping time conjecture (`Collatz/CoeffStop.lean`, `CollatzBig/CoeffStop.lean`,
  `CollatzBig/Ext.lean`): if `n` has not dropped below itself in `j` steps then
  `2^j n^s ≤ (3n+1)^s`, which the cycle check refutes for large `n`. Below the verified range the
  verification bounds the stopping time by `1000`; `n < 2^17` is checked directly. Hence, for
  `k < 301994`, the `n ≥ 2` with stopping time `≤ k` are exactly the classes of `goodSet k`.

### Integers reaching 1 and long trajectories

```lean
theorem card_reachesOne_ge_rpow (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.log 2 / Real.log 86) ≤ 2 * #{n ≤ N | ReachesOne n}
theorem card_reachesOne_ge_rpow_krasikov : ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
    κ * (N : ℝ) ^ ((303 : ℝ) / 625) ≤ #{n ≤ N | ReachesOne n}
theorem long_stopping_log_twelve (L : ℕ) : ∃ n, 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧ (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    13 * Real.log n - 85 * Real.log 3 ≤ (13 * Real.log 2 - 6 * Real.log 3) * (L + 2 : ℕ)
```

- `Collatz/Crandall.lean`: the backward tree from `1` branches at every node (two exponents
  `3 ≤ a ≤ 8` per residue mod `9`).
- `Collatz/Krasikov.lean`: all exponents `2 ≤ a ≤ 30`, constants for the residues mod `27`, and the
  step inequality for every residue mod `81` checked by `decide +kernel`
  (`scripts/krasikov_cert.py`): Krasikov's exponent `3/7` (`card_reachesOne_ge_three_sevenths`).
- `Collatz/KrasikovGen.lean`: the same argument with the modulus, exponent and weights as parameters;
  with constants for the residues mod `3^9` (packed into one natural number) and integer weights
  certified by `W_a^625 2^(303a) ≤ 3^303 2^(40·625)`, the exponent is `303/625 = 0.4848`
  (`scripts/krasikov_gen_cert.py`; moduli `3^3 … 3^9` give `0.436 … 0.485`). Krasikov–Lagarias
  reached `0.84` with a different system of difference inequalities.
- `Collatz/LongStop.lean`, `Collatz/LongStopGen.lean`: a potential on the residues mod `3^J`
  (`scripts/longstop_cert.py`) gives backward paths from `4` in which a proportion `≥ P/Q` of the steps
  are odd. Mod `3^5` with `P/Q = 2/5` gives `γ = 1/(log 2 - (2/5) log 3) ≈ 3.94` (`long_stopping_log`);
  mod `3^10` with `P/Q = 9/20` (a packed table of 59049 entries, checked by `decide +kernel` in 27
  pieces) gives `γ = 1/(log 2 - (9/20) log 3) ≈ 5.03` (trivially `1/log 2 ≈ 1.44`; Applegate–Lagarias
  reached `6.14` with about 350 million codewords). `Collatz/LongStop12.lean` uses `3^12` with
  `P/Q = 6/13` (531441 entries in 81 packed pieces, `scripts/longstop_pot.c`, `scripts/gen_ls12.py`,
  checked in the 40 generated modules `Collatz/LS12/C*.lean`, about 5 CPU-minutes): `γ ≈ 5.38`.

### The 2-adic map

`T x = (x + par x (2x + 1)) / 2` on `ℤ_[2]` extends `kstepT` (`T_natCast`), and
`Q x = ∑' i, par (T^[i] x) 2^i` reads the parity sequence as a 2-adic integer.

```lean
noncomputable def Qequiv : ℤ_[2] ≃ᵢ ℤ_[2]                       -- isometric bijection
theorem Qequiv_conj (x : ℤ_[2]) : Qequiv (T x) = shift (Qequiv x)
theorem card_periodic {p : ℕ} (hp : 1 ≤ p) : Nat.card {x : ℤ_[2] // T^[p] x = x} = 2 ^ p
theorem periodic_rational {p : ℕ} (hp : 1 ≤ p) {x : ℤ_[2]} (hx : T^[p] x = x) :
    ∃ a b : ℤ, Odd b ∧ (b : ℤ_[2]) * x = a
theorem T_measurePreserving : MeasurePreserving T μ μ
theorem T_ergodic : Ergodic T μ
theorem T_exact (hS : ∀ n, ∃ E, MeasurableSet E ∧ S = T^[n] ⁻¹' E) : μ S = 0 ∨ μ S = 1
theorem T_mixing (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n => μ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B))
theorem paritySeq_measurePreserving : MeasurePreserving paritySeq μ bernoulli
theorem odd_fraction_ae : ∀ᵐ x ∂μ, Tendsto (fun n => (oddCount2 n x : ℝ) / n) atTop (𝓝 (1 / 2))
theorem oddCount2_clt (hZ : HasLaw Z (gaussianReal 0 (1 / 4)) P') :
    TendstoInDistribution (fun n x => ((oddCount2 n x : ℝ) - n / 2) / √n) atTop Z (fun _ => μ) P'
theorem orbit_equidistributed_mod : ∀ᵐ x ∂μ, ∀ k d : ℕ, d < 2 ^ k →
    Tendsto (fun n => #{i < n | (T^[i] x).appr k = d} / n) atTop (𝓝 (2 ^ k)⁻¹)
theorem conjecture_iff_three_mul_Q : Conjecture ↔ ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, 3 * Q (n : ℤ_[2]) = z
```

- `Collatz/Lagarias.lean`: the finite-level content (`parityVec k` permutes residues mod `2^k`,
  levels are compatible, `parityVec k (T n) = parityVec (k+1) n / 2`).
- `Collatz/TwoAdic.lean`, `Collatz/Periodic.lean`: `2^k ∣ Q x - Q y ↔ 2^k ∣ x - y`; the range is
  closed and dense. Periodic points of the shift are `a / (1 - 2^p)`.
- `Collatz/Haar.lean`: Haar measure on `ℤ_[2]` with `μ (closedBall a (2^-k)) = 2^-k`; balls form a
  π-system generating the (scoped) Borel σ-algebra.
- `Collatz/Ergodic.lean`, `Collatz/Mixing.lean`: `μ (B ∩ shift^[k] ⁻¹' E) = 2^-k μ E` for balls `B`
  of radius `2^-k`; mixing extends from cylinder sets by approximation.
- `Collatz/Bernoulli.lean`, `Collatz/LLN.lean`, `Collatz/CLT.lean`, `Collatz/Equidist.lean`: the
  parities are i.i.d. fair coins; Mathlib's strong law and CLT, and a block strong law for windows.
- `Collatz/Bernstein.lean`: `3 Q 1 = -1`; conversely the integers `3 Q (T^m n)` eventually lie in
  `{-3, -2, -1, 0}`, where `Q` is injective.

## Large verification (`CollatzBig`)

| Instance | Range | Chunks | Main theorems |
| --- | --- | --- | --- |
| `CollatzBig.All` | `n < 2^32` | 6008 (`Res*`, `Cyc*`) | `descends_below`, `cycle_length_ge` (205078) |
| `CollatzBig.Ext` | `n < 434·2^24` | +4255 (`Ext*`, `ExtCyc*`) | `descends_below`, `cycle_length_ge` (492531), `stopsBy_iff_goodSet` |
| `CollatzBig.Circuit` | — | `CircuitCert` | `no_circuit` |
| `CollatzBig.MCycle` | — | `MCycleCert` | `reachesOne_of_blocks_le_13` … `_469` |

Chunk theorems are `kallFrom (resCheck 24 256 1000) lo len = true` and similar, proved by
`decide +kernel` (the kernel has GMP-accelerated `Nat`). Chunk modules import only the Mathlib-free
`Collatz.Defs`, `Collatz.ExtDefs` or `Collatz.CoeffStopDefs`, so they compile independently on several machines. The
extension adds `256 ≤ m < 434` with a sieve over residues mod `2^20`.

```sh
gcc -O2 -o plan scripts/plan.c && ./plan 24 256 > plan.txt   # regenerate (byte-identical) chunks
python3 scripts/gen_big.py 24 256 1000 6000 8 plan.txt
gcc -O2 -o plan_ext scripts/plan_ext.c && ./plan_ext 20 4 256 434 1000 > plan_ext.txt
python3 scripts/gen_ext.py 20 4 256 434 1000 plan_ext.txt CollatzBig
lake build Collatz
scripts/distributed/run.sh WORKDIR local:16 otherhost:16      # compile all 10267 chunks with lean -o
scripts/distributed/watch.sh WORKDIR                          # completion, failures, dead workers, stalls
scripts/assemble_big.sh                                       # All, Bridge, CoeffStop, Audit
scripts/assemble_ext.sh                                       # Ext, Circuit, MCycle and their audits
```

Remote hosts need a copy of the project with `lake build Collatz.Defs Collatz.ExtDefs Collatz.CoeffStopDefs`.
The same steps run on GitHub Actions in `.github/workflows/big.yml` (200 parallel jobs).
The last clean rebuild on our machines (the 10263 `Res`/`Cyc`/`Ext` chunks from `git archive` of two
commits with byte-identical chunk sources, about 92 hours of compute, then assembled and audited)
is documented in [`CollatzBig/PROVENANCE.md`](CollatzBig/PROVENANCE.md).

## Repository layout

| Path | Content |
| --- | --- |
| `Collatz/Basic.lean`, `Descent.lean`, `Residue.lean`, `Verify.lean`, `Main.lean` | Definitions, reduction to descent, residue certificates, `n < 1024` |
| `Collatz/Defs.lean`, `Kernel.lean`, `ExtDefs.lean`, `ExtKernel.lean`, `CoeffStopDefs.lean` | Mathlib-free kernel checkers and their soundness |
| `Collatz/Cycle.lean`, `CycleBound.lean`, `NatCycles.lean`, `Circuit.lean`, `MCycle.lean` | Cycle constraints |
| `Collatz/Terras.lean`, `Korec.lean`, `StoppingTime.lean`, `StoppingDist.lean`, `TerrasD.lean`, `CoeffStop.lean` | Density and stopping times |
| `Collatz/Crandall.lean`, `Krasikov.lean`, `KrasikovGen.lean`, `LongStop.lean`, `LongStopGen.lean`, `LongStop12.lean`, `LS12/` | Integers reaching 1, long trajectories |
| `Collatz/Lagarias.lean`, `TwoAdic.lean`, `Periodic.lean`, `Haar.lean`, `Ergodic.lean`, `Mixing.lean`, `Bernoulli.lean`, `LLN.lean`, `CLT.lean`, `Equidist.lean`, `Bernstein.lean` | The 2-adic map |
| `CollatzTest/` | Axiom audit and headline statements (`lake test`) |
| `CollatzBig/` | Generated chunk modules, assembly, audits, `PROVENANCE.md` |
| `scripts/` | Generators, certificate searches, distributed build scripts |

## License

[MIT](LICENSE).
