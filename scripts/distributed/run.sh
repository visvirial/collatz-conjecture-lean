#!/bin/bash
# run.sh WORKDIR HOST:N [HOST:N ...]
# Compile every chunk module CollatzBig/{Res,Cyc}*.lean in parallel, e.g.
#   scripts/distributed/run.sh /tmp/big local:8 buildhost:24
# Remote hosts need a copy of the project (rsync without .lake) with `lake build Collatz.Defs`.
# Afterwards copy the remote CollatzBig/*.olean back and run `lake build CollatzBig`.
set -e
W=$1; shift
D=$(cd "$(dirname "$0")" && pwd)
PROJ=${PROJ:-$(cd "$D/../.." && pwd)}
mkdir -p "$W/out"; : > "$W/log"; touch "$W/queue.lock"
(cd "$PROJ/CollatzBig" && ls Res*.lean Cyc*.lean | sed 's/\.lean$//') > "$W/queue"
echo "$(wc -l < "$W/queue") jobs"
id=0
for spec in "$@"; do
  host=${spec%%:*}; n=${spec##*:}
  for _ in $(seq 1 "$n"); do
    nohup "$D/worker.sh" "$W" "$host" "$id" > /dev/null 2>&1 &
    id=$((id + 1))
  done
done
echo "$id workers started; monitor with scripts/distributed/watch.sh $W"
