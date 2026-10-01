#!/usr/bin/env python3
"""Check every Lean name and file path the paper cites.

\\lean{X} with X an identifier (letters, digits, _, ., '): must be declared in Veles/ (full name
from namespace + declaration, or a unique suffix of one), in the copied upstream definitions, or be
one of the core axioms. \\lean{...} containing spaces is an expression and is skipped. \\file{P}
must exist in the repository. A dotted name must match a declaration's full name; a short name must
match exactly one declaration (or a namespace).
Controls: a misspelt name and a missing path planted in a copy must be reported.
Usage: lean_index.py paper/main.tex [--selftest]   (exit 1 on a missing name or path)"""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORE = {"propext", "Classical.choice", "Quot.sound", "Nonempty"}

NS = set()
def declared():
    names = set()
    for d, _, fs in os.walk(os.path.join(ROOT, "Veles")):
        for f in fs:
            if not f.endswith(".lean"): continue
            src = open(os.path.join(d, f)).read()
            src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
            ns = []
            for ln in src.splitlines():
                m = re.match(r"\s*namespace\s+([\w.]+)", ln)
                if m:
                    ns.append(m.group(1)); names.add(".".join(ns)); NS.add(m.group(1).split(".")[-1]); continue
                m = re.match(r"\s*end\s+([\w.]+)\s*$", ln)
                if m and ns and ns[-1] == m.group(1): ns.pop(); continue
                m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:protected |private |noncomputable )*(?:theorem|lemma|def|abbrev|structure|instance)\s+([\w.'«»]+)", ln)
                if m:
                    nm = m.group(1)
                    full = ".".join(ns + [nm]) if ns else nm
                    names.add(full); names.add(nm)
    return names

def check(tex, names):
    full = {n for n in names if "." in n}
    nsnames = NS
    bad = []
    for x in re.findall(r"\\lean\{([^}]*)\}", tex):
        x = x.replace("\\_", "_")
        if " " in x or x in CORE: continue
        if "." in x:
            if x in full or (x.split(".")[0] in ("Erdos835", "SimpleGraph", "SteinerSystems", "Nat") and x in names): continue
        else:
            hits = {n for n in full if n.split(".")[-1] == x}
            if len(hits) == 1 or x in nsnames: continue
            if len(hits) > 1:
                bad.append(f"AMBIGUOUS short Lean name: {x} ({sorted(hits)[:3]})"); continue
        bad.append(f"MISSING Lean name: {x}")
    for p in re.findall(r"\\file\{([^}]*)\}", tex):
        p = p.replace("\\_", "_")
        if not os.path.exists(os.path.join(ROOT, p)):
            bad.append(f"MISSING path: {p}")
    return bad

if __name__ == "__main__":
    tex = open(sys.argv[1]).read(); names = declared()
    bad = check(tex, names)
    ctl = check(r"\lean{Veles.J835.property\_iff\_chromaticNumbr} \file{scripts/no\_such.py}", names)
    if len(ctl) != 2:
        print("CONTROL FAIL: planted errors not caught", ctl); sys.exit(1)
    for b in bad: print(b)
    n = len(re.findall(r"\\lean\{", tex))
    print(f"LEAN INDEX: {'FAIL' if bad else 'PASS'} ({n} \\lean names, {tex.count(chr(92) + 'file{')} paths; controls caught)")
    sys.exit(1 if bad else 0)
