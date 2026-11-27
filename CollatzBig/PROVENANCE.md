# Provenance of the 2^32 verification

## Clean rebuild of 2026-11-27

All 6008 chunk modules (`CollatzBig/Res0000`-`Res5999`, `Cyc000`-`Cyc007`) were recompiled
from scratch with `lean -o`, from `git archive` of commit
`8878d4d3e746f576d97dc5f3c11761a7968267e7` only (no build products reused), toolchain
`leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.

| Host | Workers | Chunks | CPU time |
| --- | --- | --- | --- |
| LAN server (32 cores) | 16 | 3851 | 37.9 h |
| desktop (32 cores) | 8 | 2157 | 16.0 h |
| **total** | 24 | **6008** | **53.9 h** |

- Wall clock: 12:28 to 14:51 (local time), 6008 OK, 0 failures.
- Chunk sources (`Collatz/Defs.lean`, `CollatzBig/Res*.lean`, `CollatzBig/Cyc*.lean`, concatenated
  in `ls` order): sha256 `ef5c2ab556768f3c85af67902ee30bb2e211960d0baaad3b03370bb33d986dac`.
- Chunk build products (`Res*.olean`, `Cyc*.olean`, concatenated): sha256
  `adaab1617bd8384f15b92c3d2bd48573dbb5a38f6daed6176b3f12ca09fc9731`.
- The chunk sources and `Collatz/Defs.lean` are byte-identical in commit
  `49a126ab5a981aafcabc961c4ea6deca50a3b575` (checked with `cmp`). On top of the rebuilt chunks,
  that commit was assembled with `scripts/assemble_big.sh` (`lake build Collatz`, then `lean -o`
  for `Cst0`-`Cst3`, `All`, `Bridge`, `CoeffStop`, `Audit`); `CollatzBig/Audit.lean` passed, i.e.
  `descends_below`, `cycle_length_ge`, `kstepT_period_ge`, `natCast_periodic_ge`,
  `stops_at_coeff_stop` and `stopsBy_iff_goodSet` depend only on `propext`, `Classical.choice`
  and `Quot.sound`.

## How to reproduce

```sh
gcc -O2 -o plan scripts/plan.c && ./plan 24 256 > plan.txt
python3 scripts/gen_big.py 24 256 1000 6000 8 plan.txt   # byte-identical to the committed chunks
lake build Collatz
scripts/distributed/run.sh WORKDIR local:16 otherhost:16
scripts/distributed/watch.sh WORKDIR
scripts/assemble_big.sh
```

A chunk takes 30-45 s and about 4.5 GB of memory.
