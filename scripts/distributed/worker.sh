#!/bin/bash
# worker.sh WORKDIR HOST ID
# Pop chunk module names from WORKDIR/queue and compile them with `lean -o`, either locally
# (HOST=local) or over ssh on HOST, where the project is at $REMOTE_PROJ (default
# ~/collatz-work/proj) with Collatz.Defs already built. Results go to WORKDIR/log.
W=$1; HOST=$2; ID=$3
PROJ=${PROJ:-$(cd "$(dirname "$0")/../.." && pwd)}
REMOTE_PROJ=${REMOTE_PROJ:-collatz-work/proj}
TOOLCHAIN=${TOOLCHAIN:-.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean}
# one ssh master per group of workers (sshd's MaxSessions limits sessions per master)
CTL="-o ControlMaster=auto -o ControlPath=${CM_DIR:-/tmp}/cm-%C-$((ID / 8)) -o ControlPersist=600"
CMD="LEAN_PATH=.lake/build/lib/lean nice -n 10"
while true; do
  job=$(flock "$W/queue.lock" bash -c "head -1 '$W/queue'; sed -i 1d '$W/queue'")
  [ -z "$job" ] && exit 0
  t0=$(date +%s)
  if [ "$HOST" = local ]; then
    (cd "$PROJ" && eval $CMD "$HOME/$TOOLCHAIN" \
      -o .lake/build/lib/lean/CollatzBig/$job.olean CollatzBig/$job.lean) > "$W/out/$job.txt" 2>&1
  else
    ssh $CTL "$HOST" "cd $REMOTE_PROJ && $CMD ~/$TOOLCHAIN \
      -o .lake/build/lib/lean/CollatzBig/$job.olean CollatzBig/$job.lean" > "$W/out/$job.txt" 2>&1
  fi
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 255 ]; then  # ssh failure (e.g. session refused): requeue
    flock "$W/queue.lock" bash -c "echo $job >> '$W/queue'"
    echo "$(date +%T) SSHFAIL $job $HOST$ID" >> "$W/log"; sleep 30; continue
  fi
  [ $rc -eq 0 ] && st=OK || st=FAIL
  echo "$(date +%T) $st $job $HOST$ID $((t1 - t0))s" >> "$W/log"
done
