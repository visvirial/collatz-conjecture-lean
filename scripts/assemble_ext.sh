#!/bin/bash
# assemble_ext.sh: after CollatzBig is assembled (scripts/assemble_big.sh) and the extension chunks
# CollatzBig/Ext####.lean, ExtCyc###.lean are compiled (lean -o, e.g. scripts/distributed), compile
# CollatzBig/Ext.lean and the axiom audit CollatzBig/ExtAudit.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
O=.lake/build/lib/lean/CollatzBig
missing=0
for f in CollatzBig/Ext[0-9]*.lean CollatzBig/ExtCyc*.lean; do
  b=$(basename "$f" .lean)
  [ -f "$O/$b.olean" ] && [ "$O/$b.olean" -nt "$f" ] || { echo "missing or stale: $b"; missing=1; }
done
[ $missing -eq 0 ] || exit 1
for m in Ext ExtAudit; do
  echo "compiling CollatzBig.$m"
  /usr/bin/time -f "  %e s, %M KB" lake env lean -o "$O/$m.olean" "CollatzBig/$m.lean"
done
echo "extension assembled; axiom audit passed"
