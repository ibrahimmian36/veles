#!/bin/bash
# Publication gate (run on a large machine). Usage: scripts/pod_gate.sh [--dev] [P]
#   default (freeze): deletes build/, regenerates the certificate modules from certs/, rebuilds
#   every module from source, P at a time, and runs every check. --dev reuses build/ (modules whose
#   .olean is newer than their source) and marks the result DEV; a DEV log never passes freeze.
# Checks, in order: toolchain = lean-toolchain; Mathlib rev = lakefile.toml; source scan; upstream
# check; certificate regeneration and SHA256SUMS; build; manifest (Veles/AxiomCheck.lean: every
# listed theorem within propext, Classical.choice, Quot.sound); library-wide audit
# (Veles/AxiomAudit.lean); independent kernel replay of the hand-written modules (leanchecker).
# Prints START/END lines with the source hash (scripts/src_hash.sh) and generated-module hash.
# Needs LEAN_PATH listing the Mathlib build (e.g. `lake env printenv LEAN_PATH` in a project that
# requires this Mathlib) and lean/leanchecker of the pinned toolchain on PATH.
set -uo pipefail
cd "$(dirname "$0")/.."
DEV=""; [ "${1:-}" = "--dev" ] && { DEV=1; shift; }
P=${1:-16}
echo "START $(date -u +%Y-%m-%dT%H:%M:%SZ) mode=${DEV:+DEV}${DEV:-FREEZE} src-hash $(scripts/src_hash.sh)"
echo "host: $(nproc 2>/dev/null || sysctl -n hw.ncpu) cores, $P parallel builds"
fail() { echo "GATE: FAIL ($*)"; echo "END $(date -u +%Y-%m-%dT%H:%M:%SZ)"; exit 1; }
want_tc=$(sed 's/.*://' lean-toolchain); have_tc=$(lean --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p')
[ "v$have_tc" = "$want_tc" ] || fail "lean $have_tc, lean-toolchain wants $want_tc"
echo "lean $(lean --version)"
: "${LEAN_PATH:?set LEAN_PATH to the Mathlib build}"
for e in $(echo "$LEAN_PATH" | tr ':' ' '); do
  { [ -e "$e/Veles" ] || [ -e "$e/Veles.olean" ]; } && fail "LEAN_PATH entry $e contains Veles build files"
done
mlroot=$(echo "$LEAN_PATH" | tr ':' '\n' | grep '/mathlib/.lake/build/lib/lean$' | head -1 | sed 's|/.lake/build/lib/lean$||')
want_ml=$(sed -n 's/^rev = "\([0-9a-f]*\)".*/\1/p' lakefile.toml); have_ml=$(git -C "$mlroot" rev-parse HEAD 2>/dev/null)
[ "$have_ml" = "$want_ml" ] || fail "Mathlib at $have_ml, lakefile.toml pins $want_ml"
echo "mathlib $have_ml"
export LEAN_PATH="$(pwd)/build:$LEAN_PATH"
python3 scripts/scan_sources.py | tail -1 || fail "source scan"
python3 scripts/scan_sources.py > /dev/null || fail "source scan"
python3 scripts/check_upstream.py | tail -1; python3 scripts/check_upstream.py > /dev/null || fail "upstream check"
if [ -z "$DEV" ]; then
  rm -rf build
  scripts/regen_certs.sh --emit-only || fail "certificate emission"
fi
python3 scripts/scan_sources.py | tail -1; python3 scripts/scan_sources.py > /dev/null || fail "source scan after emission"
echo "gen-hash $(scripts/gen_hash.sh)"
mods=$(find Veles -name '*.lean' ! -name AxiomCheck.lean ! -name AxiomAudit.lean | sed 's/\.lean$//' | LC_ALL=C sort)
python3 scripts/build_parallel.py ${DEV:+--skip-built} "$P" $mods Veles || fail "build"
out=$(lean --root=. Veles/AxiomCheck.lean 2>&1); st=$?
echo "$out" | tail -n 3
[ $st -eq 0 ] || fail "AxiomCheck did not compile"
flat=$(echo "$out" | tr '\n' ' ' | sed 's/depends on axioms/\n&/g')
viol=$(echo "$flat" | grep "depends on axioms" | sed 's/.*axioms: \[//; s/\].*//' | tr ',' '\n' | tr -d ' ' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' | grep . || true)
count=$(echo "$out" | grep -cE "depends on axioms|does not depend on any axioms")
listed=$(grep -c '^#print axioms' Veles/AxiomCheck.lean)
[ -z "$viol" ] || fail "disallowed axioms: $viol"
echo "$out" | grep -qE "sorryAx|_native|ofReduce" && fail "sorryAx or native axiom"
[ "$count" -eq "$listed" ] || fail "$listed listed, $count reported"
aud=$(lean --root=. Veles/AxiomAudit.lean 2>&1); ast=$?
echo "$aud" | tail -n 3
[ $ast -eq 0 ] || fail "audit"
audited=$(echo "$aud" | sed -n 's/.*AXIOM AUDIT: PASS: \([0-9][0-9]*\) theorems.*/\1/p' | head -1)
{ [ -n "$audited" ] && [ "$audited" -ge "$count" ]; } || fail "audit count"
hand=$(echo "$mods" | grep -vE '^Veles/(Cert15|LS4511|LS5612)(/|$)' | tr '/' '.')
# independent replay of every declaration of the hand-written modules through a fresh kernel; the
# generated certificate modules are kernel-checked by the build itself (re-replaying them would
# repeat ~17 hours of `decide +kernel`) and pass the source scan
mkdir -p build/leanchecker
echo "$hand" | xargs -P 8 -I{} sh -c 'timeout 7200 leanchecker {} > build/leanchecker/{}.log 2>&1 || echo FAILED {}' > build/leanchecker/failures.txt
[ -s build/leanchecker/failures.txt ] && { cat build/leanchecker/failures.txt; fail "leanchecker"; }
replayed=$(echo "$hand" | grep -c .)
echo "leanchecker: $replayed modules replayed (all modules outside the three large certificates)"
echo "GATE: PASS${DEV:+ (DEV, reused build)} ($count manifest theorems, $audited theorems audited, $replayed modules replayed by leanchecker; axioms within {propext, Classical.choice, Quot.sound})"
echo "END $(date -u +%Y-%m-%dT%H:%M:%SZ)"
