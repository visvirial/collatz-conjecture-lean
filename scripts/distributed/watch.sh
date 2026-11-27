#!/bin/bash
# watch.sh WORKDIR [INTERVAL] [STALL]
# Report progress every INTERVAL seconds (default 300). Exits with a message when all jobs
# are done, on any real failure, when the workers died with jobs left, or when no job has
# finished for STALL seconds (default 900).
W=$1; INT=${2:-300}; STALL=${3:-900}
last=$(grep -c " OK " "$W/log"); since=$(date +%s)
while true; do
  sleep "$INT"
  ok=$(grep -c " OK " "$W/log"); q=$(wc -l < "$W/queue")
  # count worker processes by their exact script path, not by a pattern this script contains
  nw=$(ps -eo args= | awk -v w="$W" '$1 ~ /worker\.sh$/ || ($1 ~ /bash$/ && $2 ~ /worker\.sh$/) { if (index($0, w)) n++ } END { print n + 0 }')
  if grep " FAIL " "$W/log" | grep -qv SSHFAIL; then echo "FAIL: $(grep ' FAIL ' "$W/log" | grep -v SSHFAIL | head -3)"; exit 1; fi
  if [ "$q" -eq 0 ] && [ "$nw" -eq 0 ]; then echo "DONE: $ok OK"; exit 0; fi
  if [ "$nw" -eq 0 ]; then echo "WORKERS DIED: queue=$q"; exit 1; fi
  [ "$ok" -ne "$last" ] && { last=$ok; since=$(date +%s); }
  if [ $(( $(date +%s) - since )) -ge "$STALL" ]; then echo "STALLED: no progress for ${STALL}s (ok=$ok queue=$q)"; exit 1; fi
  echo "$(date +%T) ok=$ok queue=$q workers=$nw"
done
