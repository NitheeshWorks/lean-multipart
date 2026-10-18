#!/usr/bin/env bash
# Native time and memory checks. Each case runs in its own process; the
# bounds are in tests/Bench.lean (`bounds`).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# Heavy runs go through the workspace cap when it exists (not in CI).
CAPPED=""
if [[ -x ../stack-tools/capped ]]; then CAPPED=../stack-tools/capped; fi
$CAPPED lake build bench >/dev/null || exit 1
fail=0
for c in url50 mp50 mpMany qsMany options cl1m cl10m cl10mx qs-plain-1 qs-plain-10 qs-plain-50 qs-escaped-1 qs-escaped-10 qs-escaped-50 qs-mixed-1 qs-mixed-10 qs-mixed-50 name-1 name-2 name-4 name-over file50 fileBin50 stream50 percent50; do
  out=$($CAPPED ./.lake/build/bin/bench "$c"); status=$?
  grep -E '^(RESULT|  FAIL)' <<<"$out"
  if (( status != 0 )); then fail=1; fi
done
exit $fail
