#!/bin/bash
# Regenerate every certificate with both generators, compare with certs/SHA256SUMS, and emit the
# Lean modules. Usage:
#   scripts/regen_certs.sh [--emit-only | --both]
#   --emit-only: decompress, check SHA256SUMS, emit Lean only.
#   default: also regenerate every certificate with certgen/gen_cert.c (~3 min) and compare.
#   --both: also run the independent Python generator certgen/gen_cert_b.py (needs numpy; hours
#   for cert15) and the independent replay certgen/verify_cert.py.
set -euo pipefail
cd "$(dirname "$0")/.."
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
for f in certs/*.txt.xz; do xz -dkc "$f" > "$W/$(basename "${f%.xz}")"; done
if ! ( cd "$W" && (sha256sum *.txt 2>/dev/null || shasum -a 256 *.txt) ) | diff - certs/SHA256SUMS; then
  echo "certificate files do not match certs/SHA256SUMS"; exit 1; fi
echo "certificate files match SHA256SUMS"
python3 - "$W" <<'PY'
import sys, itertools
W = sys.argv[1]
def pre(n, m, k):
    return [sum(1 << p for p in c) for c in itertools.combinations(range(n + m), k) if sum(1 for p in c if p >= n) >= 2]
for name, n, m, k in [("ls237", 7, 5, 3), ("ls348", 8, 5, 4), ("ls4511", 11, 7, 5), ("ls5612", 12, 7, 6)]:
    open(f"{W}/{name}_pre.txt", "w").write("\n".join(map(str, pre(n, m, k))) + "\n")
open(f"{W}/ph15.txt", "w").write("24576\n16384\n"); open(f"{W}/ph9.txt", "w").write("256\n")
open(f"{W}/phnone.txt", "w").write("1\n"); open(f"{W}/phc11.txt", "w").write("2048\n4096\n8192\n")
open(f"{W}/phc12.txt", "w").write("4096\n8192\n16384\n")
PY
# name k v D DP phases pre --pre-args
SPECS="cert15:5:15:10:1:ph15:-: cert9:4:9:4:1:ph9:-: ls237:4:12:6:1:phnone:ls237_pre:7,5 ls348:5:13:6:1:phnone:ls348_pre:8,5 ls4511:6:18:8:3:phc11:ls4511_pre:11,7 ls5612:7:19:8:3:phc12:ls5612_pre:12,7"
if [ "${1:-}" = "--both" ]; then
  # independent checks: Python generator (needs numpy; hours for cert15) and Python replay
  for s in $SPECS; do IFS=: read -r nm k v D DP ph pre pa <<< "$s"
    if [ "$pre" = "-" ]; then python3 certgen/gen_cert_b.py $k $v $D $DP "$W/$ph.txt" - > "$W/py_$nm.txt" 2>/dev/null
    else START_ITEMS="$W/$pre.txt" python3 certgen/gen_cert_b.py $k $v $D $DP "$W/$ph.txt" - > "$W/py_$nm.txt" 2>/dev/null; fi
    cmp -s "$W/py_$nm.txt" "$W/$nm.txt" && echo "gen_cert_b.py reproduces $nm" || { echo "MISMATCH (python) $nm"; exit 1; }
    if [ "$pre" = "-" ]; then python3 certgen/verify_cert.py $k $v "$W/$nm.txt" | cut -c1-60
    else python3 certgen/verify_cert.py $k $v "$W/$nm.txt" - "$W/$pre.txt" | cut -c1-60; fi
  done
fi
if [ "${1:-}" != "--emit-only" ]; then
  cc -O2 -o "$W/gen_cert" certgen/gen_cert.c
  for s in $SPECS; do IFS=: read -r nm k v D DP ph pre pa <<< "$s"
    if [ "$pre" = "-" ]; then "$W/gen_cert" $k $v $D $DP "$W/$ph.txt" - > "$W/re_$nm.txt" 2>/dev/null
    else START_ITEMS="$W/$pre.txt" "$W/gen_cert" $k $v $D $DP "$W/$ph.txt" - > "$W/re_$nm.txt" 2>/dev/null; fi
    cmp -s "$W/re_$nm.txt" "$W/$nm.txt" && echo "gen_cert.c reproduces $nm" || { echo "MISMATCH $nm"; exit 1; }
  done
fi
for s in $SPECS; do IFS=: read -r nm k v D DP ph pre pa <<< "$s"
  NAME=$(echo "$nm" | sed 's/^cert/Cert/; s/^ls/LS/')
  rm -rf "Veles/$NAME" "Veles/$NAME.lean"
  if [ "$pre" = "-" ]; then python3 certgen/emit_lean.py $k $v "$W/$nm.txt" "$NAME" 2000 "$W/split_$nm" > /dev/null
  else python3 certgen/emit_lean.py $k $v "$W/$nm.txt" "$NAME" 2000 "$W/split_$nm" --pre ${pa%,*} ${pa#*,} --combs > /dev/null; fi
  echo "emitted Veles/$NAME"
done
