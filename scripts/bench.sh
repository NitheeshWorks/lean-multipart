#!/usr/bin/env bash
# Native time and memory checks. Each case runs in its own process.
#   case  max-ms  max-peak-in-units-of-body (plus a 64 MB runtime baseline)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build bench >/dev/null
fail=0
check() {
  local case=$1 maxms=$2 factor=$3
  local line
  line=$(./.lake/build/bin/bench "$case" | grep '^RESULT')
  echo "$line"
  local size ms peak
  size=$(sed -E 's/.*size=([0-9]+).*/\1/' <<<"$line")
  ms=$(sed -E 's/.*ms=([0-9]+).*/\1/' <<<"$line")
  peak=$(sed -E 's/.*peakKB=([0-9]+).*/\1/' <<<"$line")
  local limitkb=$(( size * factor / 1024 + 65536 ))
  if (( ms > maxms )); then echo "  FAIL time $ms ms > $maxms ms"; fail=1; fi
  if (( peak > limitkb )); then echo "  FAIL memory ${peak} KB > ${limitkb} KB"; fail=1; fi
}
# Limits reached early: fast, and memory is the body plus little.
check url50    500 3
check mp50     500 3
check mpMany  1000 3
check qsMany   500 3
check options  100 3
# Whole 50 MB parses and streams: linear, memory a small multiple of the body.
check file50  8000 3
check stream50 15000 3
check percent50 10000 8
exit $fail
