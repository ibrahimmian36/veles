#!/usr/bin/env python3
"""Check every number the paper states against recomputed facts, with controls that must fail.

Sources of truth: docs/ledger/facts.json (written on the build machine by scripts/cert_facts.py
from the raw certificate files and the full-gate build log) and direct recomputation here (case
table, bridge depths, symmetry primes, divisibility). Controls: a corrupted table entry, a
corrupted text number and a corrupted case-table row must each be reported.
Usage: verify_paper_claims.py paper/main.tex   (exit 1 on any mismatch)"""
import json, os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FACTS = os.path.join(ROOT, "docs", "ledger", "facts.json")

def isprime(n): return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))
def num(x): return int(x.replace("{,}", "").replace(",", ""))

ROWS = {"S(4,5,15)": "cert15", r"\LS(3,4,8)": "ls348", r"\LS(2,3,7)": "ls237",
        r"\LS(5,6,12)": "ls5612", r"\LS(4,5,11)": "ls4511", "S(3,4,9)": "cert9"}

def check(tex, facts):
    bad = []
    # certificate table
    for label, key in ROWS.items():
        m = re.search(r"\$" + re.escape(label) + r"\$(?: \(test\))? & ([\d{},]+) & (\d+) & ([\d{},]+) & ([\d{},]+) & (\w+) \\\\", tex)
        if not m: bad.append(f"table row {label} not found"); continue
        f = facts[key]
        got = (num(m[1]), int(m[2]), num(m[3]), num(m[4]), m[5])
        if f["log_fail"] or not f["log_all_ok"]: bad.append(f"{key}: build log has a failure or no ALL OK")
        want = (f["branch_nodes"], f["trees"], f["reductions"], f["modules_ok"], "yes" if f["generators_agree"] else "no")
        if got != want: bad.append(f"table row {label}: paper {got} vs facts {want}")
    c = facts["cert15"]
    # the phase-2 representatives: the trees whose root has the largest number of blocks
    top = max(c["tree_nb"]); reps = sorted(n for n, b in zip(c["tree_nodes"], c["tree_nb"]) if b == top)
    if len(reps) != 4: bad.append(f"expected 4 phase-2 representatives, found {len(reps)}")
    need = {
        "$1{,}944{,}980$ branch nodes in 24 trees with $1{,}237$ reductions":
            (c["branch_nodes"], c["trees"], c["reductions"]) == (1944980, 24, 1237),
        f"into ${c['split_trees']:,}$ trees of at most ${c['split_max_nodes']:,}$".replace(",", "{,}"): True,
        f"in ${c['log_wall_s']:,}$ seconds".replace(",", "{,}"): c["log_all_ok"] and not c["log_fail"],
        f"in ${reps[0]:,}$ to ${reps[-1]:,}$ branch nodes".replace(",", "{,}"): True,
        f"have ${facts['ls5612']['branch_nodes']:,}$ and ${facts['ls4511']['branch_nodes']:,}$ branch nodes".replace(",", "{,}"): True,
    }
    for phrase, ok in need.items():
        if phrase not in tex: bad.append(f"text lacks: {phrase}")
        elif not ok: bad.append(f"fact behind '{phrase}' does not hold")
    # resources: wall time, CPU-hours, memory, gate counts, from the freeze log via facts.json
    if facts.get("peak_rss_gib") is None: bad.append("facts.json has no peak memory (gate log predates memory logging)")
    elif f"needed at most ${facts['peak_rss_gib']:.1f}$\\,GiB" not in tex: bad.append(f"text lacks the peak memory {facts['peak_rss_gib']:.1f} GiB")
    cpu = sum(v["module_cpu_s"] for v in facts.values() if isinstance(v, dict)) / 3600
    if f"${c['log_wall_s']:,}$ seconds".replace(",", "{,}") not in tex: bad.append("build wall time")
    if f"took ${cpu:.1f}$ module build hours" not in tex: bad.append(f"text lacks total module build hours {cpu:.1f}")
    if f"took ${c['module_cpu_s'] / 3600:.1f}$ module build hours" not in tex: bad.append("S(4,5,15) module build hours")
    # case table: composite examples, first open primes, bridge end, symmetry primes
    comp = [k for k in range(3, 16) if not isprime(k + 1)]
    if "($" + ",".join(map(str, comp)) + r",\dots$)" not in tex.replace(" ", ""):
        bad.append(f"case table composite list is not {comp}")
    opens = [k for k in range(17, 193) if isprime(k + 1)]
    if "$" + ", ".join(map(str, opens[:4])) + r", \dots, " + str(opens[-1]) + "$" not in tex:
        bad.append(f"case table open list should start {opens[:4]} and end {opens[-1]}")
    for k in range(7, 193):
        d = 0 if k <= 10 else (k - 10 if k <= 189 else 2 * k - 199)
        t, kk, n = k - 1 - d, k - d, 2 * k - d
        if not (n > kk > t > 5 and t < 10 and n < 200 and d <= k - 1): bad.append(f"bridge depth fails at k={k}")
    window = [k for k in range(1, 400) if any(6 <= k - 1 - d <= 9 and 2 * k - d < 200 for d in range(0, max(k - 1, 0)))]
    if window != list(range(7, 193)): bad.append("bridge window is not 7..192")
    primes16 = [p for p in range(2, 40) if isprime(p) and 16 + 1 < p <= 32]
    if primes16 != [19, 23, 29, 31] or r"$p \in \{19,23,29,31\}$" not in tex: bad.append("k=16 primes")
    for k in range(2, 200):   # divisibility iff k+1 prime (Section 4 remark)
        from math import comb
        adm = all(comb(2 * k - i, k - 1 - i) % comb(k - i, k - 1 - i) == 0 for i in range(k))
        if adm != isprime(k + 1): bad.append(f"divisibility at k={k}")
    return bad

if __name__ == "__main__":
    tex = open(sys.argv[1]).read()
    facts = json.load(open(FACTS))
    bad = check(tex, facts)
    controls = [tex.replace("1{,}944{,}980 & 24", "1{,}944{,}981 & 24", 1),
                tex.replace("with $1{,}237$ reductions", "with $1{,}238$ reductions", 1),
                tex.replace(r"\dots, 192$", r"\dots, 190$", 1)]
    for i, ctl in enumerate(controls):
        if len(check(ctl, facts)) <= len(bad):
            print(f"CONTROL {i} FAIL: corruption not caught"); sys.exit(1)
    for b in bad: print(b)
    print(f"PAPER CLAIMS: {'FAIL' if bad else 'PASS'} ({len(bad)} findings; {len(controls)} controls caught)")
    sys.exit(1 if bad else 0)
