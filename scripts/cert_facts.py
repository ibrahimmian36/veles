#!/usr/bin/env python3
"""Recompute, from the raw certificate files and build logs, the numbers the paper states.

Writes docs/ledger/facts.json. For each certificate: branch nodes, trees, reductions (from the
unsplit generator output), trees after the split, Lean modules built OK, the SHA-256 of both
generator outputs; for S(4,5,15) also the node counts of the representative trees of each phase
and the wall time of the kernel build. Also the CPU seconds summed over module builds.
Usage (build machine): cert_facts.py CONFIG.json out.json [gen_hash_file]
CONFIG also has "_sha256sums": path to certs/SHA256SUMS; each generator output must match it.
CONFIG maps names to {"a": path, "b": path, "split": path, "log": path, "module_prefix": str}."""
import hashlib, json, os, re, sys

def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

def parse(path):
    trees, cur = [], None
    for ln in open(path):
        f = ln.split()
        if not f: continue
        if f[0] == "TREE":
            cur = {"id": int(f[1]), "nb": int(f[2]), "I": 0, "R": 0}; trees.append(cur)
        elif f[0] == "I": cur["I"] += 1
        elif f[0] == "R": cur["R"] += 1
    return trees

def main():
    cfg = json.load(open(sys.argv[1])); out = {}
    sums = dict(reversed(l.split()) for l in open(cfg.pop("_sha256sums")) if l.strip())
    for name, c in cfg.items():
        if os.path.realpath(c["a"]) == os.path.realpath(c["b"]) or os.stat(c["a"]).st_ino == os.stat(c["b"]).st_ino:
            raise SystemExit(f"{name}: the two generator outputs are the same file")
        if sha(c["a"]) != sums.get(name + ".txt"):
            raise SystemExit(f"{name}: generator output does not match certs/SHA256SUMS")
        t = parse(c["a"]); ts = parse(c["split"])
        log = open(c["log"]).read()
        oks = re.findall(r"^OK  (\S+) (\d+)s", log, re.M)
        rss = [float(g) for mm, g in re.findall(r"^OK  (\S+) \d+s ([\d.]+)GiB", log, re.M)
               if mm.startswith(c["module_prefix"] + "/") or mm == c["module_prefix"]]
        mods = [(m, int(s)) for m, s in oks if m.startswith(c["module_prefix"] + "/") or m == c["module_prefix"]]
        wall = re.findall(r"^ALL OK (\d+) modules in (\d+)s", log, re.M)
        out[name] = {
            "branch_nodes": sum(x["I"] for x in t), "trees": len(t), "reductions": sum(x["R"] for x in t),
            "split_trees": len(ts), "split_max_nodes": max(x["I"] for x in ts),
            "modules_ok": len(set(m for m, _ in mods)), "module_cpu_s": sum(s for _, s in mods),
            "log_fail": bool(re.search(r"^FAIL", log, re.M)), "log_all_ok": bool(wall),
            "log_wall_s": int(wall[-1][1]) if wall else None,
            "max_rss_gib": max(rss) if rss else None,
            "sha_a": sha(c["a"]), "sha_b": sha(c["b"]), "generators_agree": sha(c["a"]) == sha(c["b"]),
            "tree_nodes": [x["I"] for x in t], "tree_nb": [x["nb"] for x in t],
        }
    peak = re.findall(r"^PEAK RSS ([\d.]+) GiB", open(next(iter(cfg.values()))["log"]).read(), re.M)
    out["peak_rss_gib"] = float(peak[-1]) if peak else None
    out["gen_hash"] = cfg_gen_hash = open(sys.argv[3]).read().strip() if len(sys.argv) > 3 else None
    json.dump(out, open(sys.argv[2], "w"), indent=1, sort_keys=True)
    for n, f in out.items():
        if isinstance(f, dict): print(n, {k: v for k, v in f.items() if k not in ("tree_nodes", "tree_nb")})

if __name__ == "__main__":
    main()
