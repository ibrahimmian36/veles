#!/usr/bin/env python3
"""Write the append-only JSONL ledger of one refutation certificate (run on the build machine).

Every ledger starts with a header whose status is "exhausted": the search behind the certificate
is exhaustive (every branch is explored or reduced by a checked permutation), not sampled.
Records: parameters; the two independent generator outputs (gen_cert.c, gen_cert_b.py) with their
SHA-256 (they must be equal); the independent replay (verify_cert.py); the split certificate; the
kernel build summary. The script recomputes every hash and re-runs the replay; it fails if the two
generator outputs differ or if a replay fails.

Usage: make_ledger.py NAME k v D DP phasefile startitems|- a_out b_out split_txt buildlog out.jsonl
"""
import hashlib, json, os, re, subprocess, sys, datetime

def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

def main():
    (name, k, v, D, DP, phf, pre, a_out, b_out, split, blog, out) = sys.argv[1:13]
    here = os.path.dirname(os.path.abspath(__file__))
    ver = os.path.join(here, "..", "certgen", "verify_cert.py")
    recs = []
    phases = [int(x) for x in open(phf).read().split()]
    recs.append({"kind": "header", "status": "exhausted", "certificate": name,
                 "claim": f"no exact cover of the {int(k)-1}-subsets of range({v}) by {k}-subsets"
                          + (" extending the pre-covered items" if pre != "-" else ""),
                 "date": datetime.date.today().isoformat()})
    recs.append({"kind": "params", "k": int(k), "v": int(v), "D": int(D), "DP": int(DP),
                 "phases": phases, "pre_items_sha256": sha(pre) if pre != "-" else None,
                 "pre_items": len(open(pre).read().split()) if pre != "-" else 0})
    ha, hb = sha(a_out), sha(b_out)
    if ha != hb:
        raise SystemExit(f"LEDGER FAIL: generators differ ({ha} vs {hb})")
    for impl, p, h in (("certgen/gen_cert.c", a_out, ha), ("certgen/gen_cert_b.py", b_out, hb)):
        recs.append({"kind": "generate", "impl": impl, "sha256": h, "bytes": os.path.getsize(p)})
    args = ["python3", ver, str(k), str(v), a_out] + (["-", pre] if pre != "-" else [])
    r = subprocess.run(args, capture_output=True, text=True).stdout.strip()
    if not r.startswith("CERT PASS"):
        raise SystemExit(f"LEDGER FAIL: replay: {r}")
    m = re.match(r"CERT PASS: (\d+) trees, (\d+) branch nodes, (\d+) reductions", r)
    recs.append({"kind": "verify", "impl": "certgen/verify_cert.py", "input_sha256": ha,
                 "trees": int(m[1]), "branch_nodes": int(m[2]), "reductions": int(m[3]), "result": "PASS"})
    args = ["python3", ver, str(k), str(v), split] + (["-", pre] if pre != "-" else [])
    r = subprocess.run(args, capture_output=True, text=True).stdout.strip()
    if not r.startswith("CERT PASS"):
        raise SystemExit(f"LEDGER FAIL: split replay: {r}")
    m2 = re.match(r"CERT PASS: (\d+) trees, (\d+) branch nodes, (\d+) reductions", r)
    if m2[2] != m[2]:
        raise SystemExit("LEDGER FAIL: split changed the number of branch nodes")
    recs.append({"kind": "split", "impl": "certgen/emit_lean.py", "sha256": sha(split),
                 "trees": int(m2[1]), "branch_nodes": int(m2[2]), "reductions": int(m2[3]), "result": "PASS"})
    log = open(blog).read()
    ok = re.findall(r"^ALL OK (\d+) modules in (\d+)s", log, re.M)
    fails = re.findall(r"^FAIL", log, re.M)
    mods = {ln.split()[1] for ln in log.splitlines() if ln.startswith("OK ")}
    prefix = "Veles/" + {"cert": "Cert", "ls": "LS"}[re.match(r"[a-z]+", name).group(0)] + name[len(re.match(r"[a-z]+", name).group(0)):]
    recs.append({"kind": "kernel", "module_prefix": prefix,
                 "modules_ok": len([x for x in mods if x == prefix or x.startswith(prefix + "/")]),
                 "build_all_ok": bool(ok) and not fails, "log_sha256": sha(blog)})
    with open(out, "a") as fh:
        for rec in recs:
            fh.write(json.dumps(rec, sort_keys=True) + "\n")
    print(f"LEDGER OK {name}: {m[2]} nodes, generators agree ({ha[:12]})")

if __name__ == "__main__":
    main()
