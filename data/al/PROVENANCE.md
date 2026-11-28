# Provenance of the Applegate–Lagarias prefix trees

Each `tree-P-Q.txt.xz` is the output of the search in `TREE` mode of `scripts/al_vec.c` (or of
`scripts/al_gpu`, which prints the same lines) for the ratio `P/Q`. The format is:

- `# TREE ...`: the parameters of the run;
- `S r m`: the class `r mod 3^m` is split into its three children;
- `L r m ok work T_1,T_2,...`: a leaf, with the result of the C mirror of the kernel check
  (`ok = 1`), its estimated kernel steps and the per-level band hints;
- `# done ...`: totals (`stage1` = stage-1 search work, `kernel` = estimated kernel steps of all
  leaves, `leaves`, `overW0` = leaves above the work limit `W0`, `fail` = failed classes).

The trees are only hints for the kernel: `scripts/gen_al.py` turns a tree into Lean modules, and
each leaf becomes a `decide +kernel` theorem about `Collatz.LSA.chunk`, whose soundness
(`Collatz.LSA.chunk_sound`) holds for any hints. A wrong or missing entry makes the Lean check fail;
it cannot make it succeed wrongly. The programs that produced the trees are therefore not part of
the trusted base. `docs/overview.md`, Section 7, describes the method and the pipeline.

Build of the search programs:

```sh
gcc -O2 -fopenmp -o al_vec scripts/al_vec.c
# GPU version (CUDA, sm_86), in a directory holding al_vec.c, al_gpu.h, al_gpu_host.c, al_gpu.cu:
make -f al_gpu.mk -j4          # builds al_gpu and the CPU-only reference al_s1ref
```

The argument order is `P Q D split Lmax Tbig sample`; `TREE="W0 mmax"` selects the tree mode and
`OFFSET=o` starts at task `o` (with `sample = s`, the tasks `o, o + s, o + 2s, ...` are processed).

## Files

| file | sha256 | commit |
| --- | --- | --- |
| `tree-4-9.txt.xz` | `192ecc253bba7d0f269e31c38d7cf723837ce95d68a170475599219145731baf` | `f33c17a` |
| `tree-28-59.txt.xz` | `af45f82d557912785638f96dff64731026e33566e89b985ebd7bbd1ae98267d3` | `45e2565` |
| `tree-14-29.txt.xz` | `84cf642ddeda754cf4a2d29c52a858114f158cc548d898e992d776a18c18ea78` | `b336bab` |

## Ratio 4/9 (`γ = 1/(log 2 - (4/9) log 3) ≈ 4.881`)

Header lines (`xz -dc tree-4-9.txt.xz | grep '^#'`):

```
# TREE P=4 Q=9 D=60 split=6 Lmax=40 Tbig=200 W0=100000 mmax=34 sample=1 offset=0
# done tasks=82 stage1=11697060922 kernel=4636128 leaves=188 overW0=0 fail=0 time=467s
```

Command:

```sh
TREE="100000 34" ./al_vec 4 9 60 6 40 200 1 > tree-4-9.txt
```

A small instance, used to test the pipeline. `gen_al.py` (budget `2·10^6`, fan-in 1000): 188 leaves,
93 inner nodes, 4 636 316 estimated steps (kernel steps plus one per leaf), 3 chunk modules,
2 assembly modules.

GitHub Actions (`.github/workflows/al.yml`, `shards = 3`, budget `2000000`), all successful:

- 46017604665: the whole check in one run (commit `f33c17a`);
- 46027927934 and 46028063910: the same check split over two runs, the second assembling with the
  shard oleans of the first (commit `9642c73`).

## Ratio 28/59 (`γ = 1/(log 2 - (28/59) log 3) ≈ 5.8217`)

Header lines:

```
# TREE P=28 Q=59 D=60 split=11 Lmax=40 Tbig=420 W0=100000 mmax=34 sample=1 offset=0
# done tasks=12038 stage1=2893805380458 kernel=4275524136 leaves=132636 overW0=0 fail=0 time=7610s
```

Command (CPU, 28 threads):

```sh
TREE="100000 34" ./al_vec 28 59 60 11 40 420 1 > tree-28-59.txt
```

`gen_al.py` (budget `2·10^6`, fan-in 1000): 132 636 leaves, 66 317 inner nodes, 4 275 656 772
estimated steps, 2903 chunk modules, 11 assembly modules, `Final` with
`Collatz.LSA.long_stopping_AL_28_59`.

Later, `scripts/al_gpu` reproduced this tree: its output (sorted lines and the `# done` line,
apart from `time=`) was byte-identical, in about 105 s on an RTX 3080 with 4 CPU threads.

GitHub Actions (`shards = 100`, budget `2000000`), all successful:

- 46032421992 and 46032440828: the chunk modules, 50 shards each (commit `45e2565`);
- 46043134239: the assembly with the shard oleans of both runs and the axiom audit (commit
  `5ad1e44`).

In total 101 jobs and 22.8 runner-hours.

## Ratio 14/29 (`γ = 1/(log 2 - (14/29) log 3) ≈ 6.14316`, the value of Applegate and Lagarias)

Header lines:

```
# TREE P=14 Q=29 D=60 split=12 Lmax=40 Tbig=200 W0=100000 mmax=40 (merged from sample=10 offsets 0-9; offsets 4-7 by scripts/al_gpu)
# done offsets=10 stage1=18895040060246 kernel=99614855878 leaves=3016916 overW0=0 fail=0 
```

The tree was searched in ten parts (`sample = 10`, offsets `0 … 9`), each part a separate run:

```sh
# offsets 0-3 and 8-9: al_vec (CPU), on two machines of the local network
TREE="100000 40" OFFSET=$o ./al_vec 14 29 60 12 40 200 10 > tree-14-29-$o.txt
# offsets 4-7: al_gpu (GPU stage 1)
TREE="100000 40" OFFSET=$o ./al_gpu 14 29 60 12 40 200 10 > tree-14-29-$o.txt
```

The environment settings of `al_gpu` (`GPU_*`, `S2CAP`) were not recorded in the file; according
to `scripts/al_gpu.cu` they change resource use and speed, not the printed lines. Partial outputs
of `al_vec` for offsets 4–7 also exist; every line of them occurs in the corresponding `al_gpu`
output.

Merging. The file holds the `S` and `L` lines of the ten outputs, sorted in C-locale order (the
classes above level `split` are printed by offset 0 only). The `# TREE` line records the merge,
and the `# done` line holds the sums over the ten parts (`stage1`, `kernel`, `leaves`, `overW0`,
`fail`; it has no `tasks` or `time` field). Checks of the merged file:

- no class occurs twice, and every leaf has `ok = 1`;
- the leaf work sums to `kernel=99614855878`, and there are 3 016 916 leaves and 1 508 457 split
  classes; the deepest leaf is at level 23;
- `gen_al.py` accepts it, which requires that every class reached from `1, 2 mod 3` is either split
  or a leaf and that no class lies outside these subtrees;
- before the full run, `al_gpu` and `al_vec` gave byte-identical outputs on `14/29` samples.

`gen_al.py` (budget `2·10^6`, fan-in 1000): 3 016 916 leaves, 1 508 457 inner nodes,
99 617 872 794 estimated steps (about `9.96·10^10`), 67 094 chunk modules, 230 assembly modules,
`Final` with `Collatz.LSA.long_stopping_AL_14_29`.

GitHub Actions (`shards = 330`, commit `b336bab`):

- 46083436083 (run A) and 46083447454 (run B): the chunk modules, 165 shards each; in progress;
- assembly: pending.

At the measured rate of about `1.9·10^8` kernel steps per runner-hour, the chunk check is roughly
520 runner-hours. Until the assembly run has succeeded, `long_stopping_AL_14_29` is not proved.
