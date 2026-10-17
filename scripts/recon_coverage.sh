#!/usr/bin/env bash
# Measure proof reconstruction coverage on the test suite.
#
# Every `#blaster` command and `blaster` tactic in the test suite is run with proof
# reconstruction activated (best effort). Every `#testOptimize` test additionally tries to
# reconstruct a kernel-checked proof that the input term is equal to its optimized form.
# One JSON line per reconstruction attempt is appended to the stats file, which is then
# summarized by `scripts/recon_report.py`.
#
# Usage: ./scripts/recon_coverage.sh [stats-file] [parallel-jobs] [path-filter]
set -u
OUT=$(realpath -m "${1:-recon_stats.jsonl}")
JOBS=${2:-4}
FILTER=${3:-Tests}
rm -f "$OUT"
lake build Tests.Utils Tests.Smt.Benchmarks.ValidatorsExamples.PlutusLedgerAPI.VDummy >/dev/null || exit 1
# leaf test files only (i.e., files that contain test commands), excluding state machine tests
FILES=$(grep -rlE "#blaster|#testOptimize|by blaster" "$FILTER" --include=*.lean \
          | grep -v "^Tests/Utils.lean" | grep -v "^Tests/StateMachine" | sort)
# watchdog: kill SMT solver instances running for more than 5 minutes (e.g., solver hangs)
( while true; do
    for p in $(pgrep -x z3); do
      e=$(ps -o etimes= -p "$p" | tr -d ' ')
      if [ -n "$e" ] && [ "$e" -gt 300 ]; then kill "$p"; fi
    done
    sleep 15
  done ) &
WATCHDOG=$!
trap 'kill $WATCHDOG 2>/dev/null' EXIT
echo "$FILES" | xargs -P "$JOBS" -I{} sh -c \
  'BLASTER_RECONSTRUCT=1 BLASTER_RECON_STATS="$0" timeout 900 lake env lean "$1" >/dev/null 2>&1 || echo "failed: $1"' "$OUT" {}
python3 "$(dirname "$0")/recon_report.py" "$OUT"
