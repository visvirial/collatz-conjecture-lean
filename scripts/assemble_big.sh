#!/bin/bash
# assemble_big.sh: after all CollatzBig chunk modules are compiled (scripts/distributed/run.sh),
# compile CollatzBig/All.lean, Bridge.lean and Audit.lean with `lean -o`. Audit.lean fails unless
# the 2^32 theorems use only propext, Classical.choice and Quot.sound.
# Needs `lake build Collatz` first. Do not use `lake build` on CollatzBig (it is not a target).
set -euo pipefail
cd "$(dirname "$0")/.."
O=.lake/build/lib/lean/CollatzBig
missing=0
for f in CollatzBig/Res*.lean CollatzBig/Cyc*.lean; do
  b=$(basename "$f" .lean)
  [ -f "$O/$b.olean" ] && [ "$O/$b.olean" -nt "$f" ] || { echo "missing or stale: $b"; missing=1; }
done
[ $missing -eq 0 ] || exit 1
for m in All Bridge Audit; do
  echo "compiling CollatzBig.$m"
  /usr/bin/time -f "  %e s, %M KB" lake env lean -o "$O/$m.olean" "CollatzBig/$m.lean"
done
echo "CollatzBig assembled; axiom audit passed"
