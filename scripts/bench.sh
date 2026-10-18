#!/usr/bin/env bash
# Native time and memory checks. Each case runs in its own process; the
# bounds are in tests/Bench.lean (`bounds`).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# Heavy runs go through the workspace cap when it exists (not in CI).
CAPPED=""
if [[ -x ../stack-tools/capped ]]; then CAPPED=../stack-tools/capped; fi
$CAPPED lake build bench >/dev/null || exit 1
# On a machine with cores of different speeds (performance and efficiency
# cores), run each case on the least busy of the fastest cores, as the Python
# references in tests/upstream/urlencoded_speed.py are taken.
PIN=""
pick_core() {
  local f n max=0 cores=() a b best="" bestidle=-1
  for f in /sys/devices/system/cpu/cpu[0-9]*/cpufreq/cpuinfo_max_freq; do
    n=${f#/sys/devices/system/cpu/cpu}; n=${n%%/*}
    if (( $(cat "$f") > max )); then max=$(cat "$f"); cores=("$n")
    elif (( $(cat "$f") == max )); then cores+=("$n"); fi
  done
  a=$(grep '^cpu[0-9]' /proc/stat); sleep 0.3; b=$(grep '^cpu[0-9]' /proc/stat)
  for n in "${cores[@]}"; do
    local i0 i1
    i0=$(awk -v c="cpu$n" '$1==c {print $5}' <<<"$a"); i1=$(awk -v c="cpu$n" '$1==c {print $5}' <<<"$b")
    if (( i1 - i0 > bestidle )); then bestidle=$(( i1 - i0 )); best=$n; fi
  done
  echo "$best"
}
if command -v taskset >/dev/null && compgen -G '/sys/devices/system/cpu/cpu[0-9]*/cpufreq/cpuinfo_max_freq' >/dev/null; then
  PINNED=1
fi
fail=0
for c in url50 mp50 mpMany qsMany options cl1m cl10m cl10mx qs-plain-1 qs-plain-10 qs-plain-50 qs-escaped-1 qs-escaped-10 qs-escaped-50 qs-mixed-1 qs-mixed-10 qs-mixed-50 qs-plus-1 qs-plus-10 qs-latin-1 qs-latin-10 name-1 name-2 name-4 name-over name-pw-1 name-pw-2 name-plus-1 name-plus-10 file50 fileBin50 stream50 percent50; do
  if [[ -n "${PINNED:-}" ]]; then core=$(pick_core); PIN="taskset -c $core"; fi
  out=$($CAPPED $PIN ./.lake/build/bin/bench "$c"); status=$?
  grep -E '^(RESULT|  FAIL)' <<<"$out" | sed "s/^RESULT/RESULT${PIN:+ [cpu $core]}/"
  if (( status != 0 )); then fail=1; fi
done
exit $fail
