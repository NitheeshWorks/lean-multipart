#!/usr/bin/env bash
# Native time and memory checks. Each case runs in its own process; the
# bounds are in tests/Bench.lean (`bounds`).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build bench >/dev/null || exit 1
fail=0
for c in url50 mp50 mpMany qsMany options file50 fileBin50 stream50 percent50; do
  out=$(./.lake/build/bin/bench "$c"); status=$?
  grep -E '^(RESULT|  FAIL)' <<<"$out"
  if (( status != 0 )); then fail=1; fi
done
exit $fail
