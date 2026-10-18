#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. The verification gate
# (scripts/Axioms.lean, `lake exe axioms`) checks every declaration on the
# compiled environment. Exits on the first failure.
#
#   scripts/check.sh            # everything
#   scripts/check.sh --quick    # build and the verification gate (no tests)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=LeanMultipart

echo "== build =="
lake build

echo "== verification gate =="
# The gate is a pinned copy of stack-tools/Axioms.lean: never edit it here.
echo "$(cat scripts/Axioms.sha256)  scripts/Axioms.lean" | sha256sum -c --quiet
lake exe axioms "$LIB"

[[ "${1:-}" == "--quick" ]] && exit 0

echo "== property tests =="
lake exe props

echo "== conformance =="
lake exe conformance

echo "== examples =="
lake exe docs-index > /dev/null
# The examples manifest check lives in the workspace's stack-tools (not in CI).
if [[ -f ../stack-tools/check-examples.py ]]; then python3 ../stack-tools/check-examples.py "$PWD"; fi

echo "== native time and memory =="
scripts/bench.sh

echo "== traceability =="
python3 scripts/traceability-check.py

if [[ "${1:-}" == "--pbt" ]]; then
  echo "== plausible =="
  (cd tests/pbt && lake build && ./.lake/build/bin/pbt)
fi
echo "all clean"
