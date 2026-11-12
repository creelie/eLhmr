#!/usr/bin/env bash
# Usage: below/run_job.sh JOB   (JOB = 0..19). Reads below/request.env, writes below/out/JOB.log.
set -euo pipefail
job=$1
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck disable=SC1091
. "$here/request.env"
gcc -O2 -o "$here/tb" "$here/../tree_below.c" -lgmp -lm
mkdir -p "$here/out"
P=$((80 * ROUNDS))
pids=()
for t in 0 1 2 3; do
  c=$((4 * job + t))
  (
    for k in $SPLIT_K; do
      for ((r = FIRST_ROUND; r < LAST_ROUND; r++)); do
        "$here/tb" "$X" "$k" --part $((c + 80 * r))/$P --splitdepth 11
      done
    done
  ) > "$here/out/core$c.log" 2>&1 &
  pids+=($!)
done
if [ "$job" = 0 ] && [ "$FIRST_ROUND" = 0 ]; then
  for k in $SMALL_K; do "$here/tb" "$X" "$k"; done > "$here/out/small.log" 2>&1
fi
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
cat "$here"/out/*.log
exit $rc
