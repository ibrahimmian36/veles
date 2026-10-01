#!/bin/bash
# Freeze check (local part, minutes). Runs every non-Lean check and validates the log of the final
# gate run (docs/verification/gate_freeze.log, written by `scripts/pod_gate.sh` in freeze mode):
# the log must come from freeze mode, pass, and carry the source hash of this tree
# (`scripts/src_hash.sh`) and the generated-module hash recorded in docs/ledger/facts.json.
# A log is a record, not a proof: anyone can rerun the gate. Exit 1 on any failure.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
out=$(mktemp); trap 'rm -f "$out"' EXIT
run() { echo "== $*"; "$@" > "$out" 2>&1 || { fail=1; echo "   FAIL"; }; tail -1 "$out"; }
run python3 scripts/scan_sources.py
run python3 scripts/check_upstream.py
run python3 scripts/lean_index.py paper/main.tex
run python3 scripts/verify_paper_claims.py paper/main.tex
run python3 scripts/check_reps.py
L=docs/verification/gate_freeze.log
echo "== gate log $L"
if [ ! -f "$L" ]; then fail=1; echo "   FAIL: missing"
else
  head -1 "$L" | grep -q "^START .* mode=FREEZE src-hash $(scripts/src_hash.sh)\$" || { fail=1; echo "   FAIL: not a freeze-mode log for the current sources"; }
  grep -q "^GATE: PASS (" "$L" || { fail=1; echo "   FAIL: gate did not pass"; }
  grep -q "DEV" "$L" && { fail=1; echo "   FAIL: DEV log"; }
  grep -q "^FAIL" "$L" && { fail=1; echo "   FAIL: a module failed"; }
  gh=$(sed -n 's/^gen-hash //p' "$L"); fh=$(python3 -c "import json;print(json.load(open('docs/ledger/facts.json'))['gen_hash'])" 2>/dev/null)
  [ -n "$gh" ] && [ "$gh" = "$fh" ] || { fail=1; echo "   FAIL: generated-module hash $gh vs facts $fh"; }
  tail -1 "$L" | grep -q "^END" || { fail=1; echo "   FAIL: incomplete log"; }
  [ $fail -eq 0 ] && echo "   log: freeze mode, passed, source hash $(scripts/src_hash.sh | cut -c1-16)... matches"
fi
[ $fail -eq 0 ] && echo "FREEZE CHECK: PASS" || echo "FREEZE CHECK: FAIL"
exit $fail
