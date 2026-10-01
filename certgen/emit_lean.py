#!/usr/bin/env python3
"""Lay a gen_cert certificate out as Lean modules replayed by the kernel.

Steps: (1) split every tree so no Lean theorem replays more than N branch nodes (a cut subtree
becomes a new tree, referenced by an identity reduction); (2) write the split certificate in the
gen_cert text format, so verify_cert.py can re-check it; (3) write one Lean module per tree.

Usage: emit_lean.py k v cert.txt NAME N OUTDIR
  writes OUTDIR/split.txt and Lean modules Veles/NAME/T<id>.lean plus Veles/NAME.lean.
Tree j's module defines `root` (its state), `ctx`, `words` and proves
  `Veles.NAME.T<j>.noExt : NoExt v k (dec root)`.
"""
import os, sys
sys.setrecursionlimit(1 << 20)
sys.set_int_max_str_digits(0)

def parse(path):
    trees, cur = {}, None
    for ln in open(path):
        f = ln.split()
        if not f:
            continue
        if f[0] == "TREE":
            nb = int(f[2]); rest = f[3 + nb:]
            cur = trees[int(f[1])] = {"blocks": [int(x) for x in f[3:3 + nb]], "nodes": [],
                                      "pre": [int(x) for x in rest[1:]] if rest else []}
        elif f[0] == "END":
            cur = None
        else:
            cur["nodes"].append(f)
    return trees

def main():
    k, v, path, name, N, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5]), sys.argv[6]
    trees = parse(path)
    items_mod = sys.argv[sys.argv.index("--items") + 1] if "--items" in sys.argv else "Veles.Items"
    use_combs = "--combs" in sys.argv          # item list `combs v t` (Veles/Combs.lean), no table
    if use_combs: items_mod = "Veles.Combs"
    il = f"(combs {v} {k - 1})" if use_combs else f"items{v}_{k - 1}"
    il_good = f"(combs_good {v} {k - 1})" if use_combs else f"(items{v}_{k - 1}_good)"
    pre = sorted(trees[0]["pre"])
    assert all(sorted(t["pre"]) == pre for t in trees.values())
    lsn = lsm = None
    if pre:
        # large-set encoding: --pre n m ; the pre-covered items must be exactly the (k-1)-sets of
        # range(n+m) with at least two colour points (>= n)
        i = sys.argv.index("--pre"); lsn, lsm = int(sys.argv[i + 1]), int(sys.argv[i + 2])
        assert lsn + lsm == v
        want = sorted(T for T in range(1 << v) if bin(T).count("1") == k - 1 and bin(T >> lsn).count("1") >= 2)
        assert pre == want, "pre-covered items are not the colour-point encoding"
    ident = ",".join(str(i) for i in range(v))

    def subs(B): return [B & ~(1 << y) for y in range(v) if B >> y & 1]

    # ---- parse each tree into a nested structure: ("I", T, [(block, child), ...]) or ("R", j, perm)
    def build(nodes, cov):
        pos = 0
        def rec():
            nonlocal pos
            f = nodes[pos]; pos += 1
            if f[0] == "R":
                return ["R", int(f[1]), f[2]]
            T = int(f[1]); kids = []
            for x in range(v):
                if T >> x & 1: continue
                B = T | 1 << x; S = subs(B)
                if any(s in cov for s in S): continue
                cov.update(S); kids.append([B, rec()]); cov.difference_update(S)
            return ["I", T, kids]
        r = rec(); assert pos == len(nodes)
        return r

    new = {}
    next_id = [max(trees) + 1]
    def size(t):
        return 0 if t[0] == "R" else 1 + sum(size(c) for _, c in t[2])
    def split(t, path_blocks):
        """Cut children of t (bottom-up) until each remaining piece has at most N branch nodes."""
        if t[0] == "R": return 0
        total = 1
        sizes = []
        for i, (B, c) in enumerate(t[2]):
            s = split(c, path_blocks + [B]); sizes.append((s, i)); total += s
        for s, i in sorted(sizes, reverse=True):
            if total <= N: break
            B, c = t[2][i]
            j = next_id[0]; next_id[0] += 1
            new[j] = {"blocks": path_blocks + [B], "tree": c}
            t[2][i] = [B, ["R", j, ident]]
            total -= s
        return total
    for j in sorted(trees):
        cov = set(pre)
        for B in trees[j]["blocks"]: cov.update(subs(B))
        t = build(trees[j]["nodes"], cov)
        new_j = {"blocks": trees[j]["blocks"], "tree": t}
        split(t, list(trees[j]["blocks"]))
        new[j] = new_j

    # ---- write split certificate in gen_cert format
    os.makedirs(outdir, exist_ok=True)
    def flat(t, out):
        if t[0] == "R": out.append(f"R {t[1]} {t[2]}"); return
        out.append(f"I {t[1]}")
        for _, c in t[2]: flat(c, out)
    with open(os.path.join(outdir, "split.txt"), "w") as fh:
        for j in sorted(new):
            fh.write(f"TREE {j} {len(new[j]['blocks'])}" + "".join(f" {b}" for b in new[j]["blocks"])
                     + ((" ITEMS" + "".join(f" {x}" for x in pre)) if pre else "") + "\n")
            out = []; flat(new[j]["tree"], out); fh.write("\n".join(out) + "\nEND\n")

    # ---- Lean modules
    mdir = os.path.join("Veles", name); os.makedirs(mdir, exist_ok=True)
    maxsz = 0
    for j in sorted(new):
        t = new[j]["tree"]
        perms, targets, fields = [], [], []
        def enc(t):
            if t[0] == "R":
                p = t[2]
                if p not in perms: perms.append(p)
                if t[1] not in targets: targets.append(t[1])
                fields.extend([0, perms.index(p), targets.index(t[1])]); return
            fields.append(t[1])
            for _, c in t[2]: enc(c)
        enc(t)
        assert all(0 <= x < 65536 for x in fields)
        maxsz = max(maxsz, size(t))
        words = []
        for i in range(0, len(fields), 256):
            w = 0
            for q, x in enumerate(fields[i:i + 256]): w |= x << (16 * q)
            words.append(w)
        if j == 0: words0 = list(words)
        imports = "".join(f"import Veles.{name}.T{tj}\n" for tj in sorted(targets))
        blocks = ", ".join(map(str, new[j]["blocks"]))
        permtxt = ", ".join("[" + p + "]" for p in perms)
        tgt = ", ".join(f"Veles.{name}.T{tj}.root" for tj in targets)
        good_t = ", ".join(f"Veles.{name}.T{tj}.noExt" for tj in targets)
        with open(os.path.join(mdir, f"T{j}.lean"), "w") as fh:
            fh.write(f"""import {items_mod}
{f"import Veles.{name}.Pre" + chr(10) if pre else ""}{imports}
/-! Generated by `certgen/emit_lean.py` from the certificate `certs/{name.lower()}.txt`. Do not edit. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Veles.{name}.T{j}
open Veles.Checker Veles.Cover Veles.Bits Veles.CertKit

/-- The state at the root of this tree. -/
def root : ℕ := stateOf {v} [{blocks}]{f" ||| Veles.{name}.Pre.pre" if pre else ""}

/-- Reduction data. -/
def ctx : Ctx := ⟨{v}, {k - 1}, {il}, [{permtxt}], [{tgt}]⟩

/-- The tree, {size(t)} branch nodes, as 16-bit fields. -/
def words : List ℕ := [{", ".join(map(str, words))}]

theorem replay : (node ctx 1000000 root ⟨words, 0, 0⟩).isSome = true := by decide +kernel

theorem noExt : NoExt {v} {k} (dec root) :=
  noExt_of_replay {il_good} (ts := [{tgt}]) (by exact {("⟨" + good_t + ", trivial⟩") if good_t else "trivial"}) replay

end Veles.{name}.T{j}
""")
    if pre:
        bits = 0
        for T in pre: bits |= 1 << T
        with open(os.path.join(mdir, "Pre.lean"), "w") as fh:
            fh.write(f"""import Veles.LargeSetCover

/-! Generated by `certgen/emit_lean.py`. Do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Veles.{name}.Pre

/-- The {len(pre)} {k - 1}-subsets of `range {v}` with at least two colour points (>= {lsn}), as a state. -/
def pre : ℕ := {bits}

theorem pre_eq : pre = Veles.LSC.preOf {lsn} {lsm} {k - 1} := by decide +kernel

end Veles.{name}.Pre
""")
    mut = [words0[0] ^ 1] + words0[1:]
    short = words0[:-1] if len(words0) > 1 else []
    controls = f"""
/-! Controls at the certificate's own parameters: tree 0's stream with its first field changed,
and with its last word removed, are rejected by the kernel. -/

namespace Veles.{name}
open Veles.Checker

theorem control_mutated :
    (node Veles.{name}.T0.ctx 1000000 Veles.{name}.T0.root ⟨[{", ".join(map(str, mut))}], 0, 0⟩).isSome = false := by
  decide +kernel

theorem control_truncated :
    (node Veles.{name}.T0.ctx 1000000 Veles.{name}.T0.root ⟨[{", ".join(map(str, short))}], 0, 0⟩).isSome = false := by
  decide +kernel

end Veles.{name}
"""
    with open(os.path.join("Veles", f"{name}.lean"), "w") as fh:
        fh.write("".join(f"import Veles.{name}.T{j}\n" for j in sorted(new)))
        fh.write("\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n")
        assert new[0]["blocks"] == [], "tree 0 must start from the empty state"
        if pre:
            fh.write(f"""
/-! Generated by `certgen/emit_lean.py`. Do not edit. -/

namespace Veles.{name}
open Veles.Cover Veles.CertKit Veles.Bits

/-- The colour-point encoding of a large set `LS({k - 2}, {k - 1}, {lsn})` of {lsm} systems has no cover. -/
theorem noExt_pre : NoExt {v} {k} (dec (Veles.LSC.preOf {lsn} {lsm} {k - 1})) := by
  have h := Veles.{name}.T0.noExt
  simp only [Veles.{name}.T0.root, stateOf_nil, Nat.zero_or] at h
  rwa [Veles.{name}.Pre.pre_eq] at h

end Veles.{name}
""" + controls)
        else:
            fh.write(f"""
/-! Generated by `certgen/emit_lean.py`. Do not edit. -/

namespace Veles.{name}
open Veles.Cover Veles.CertKit Veles.Bits

/-- No exact cover of the {k - 1}-subsets of `range {v}` by {k}-subsets exists. -/
theorem noExt_empty : NoExt {v} {k} ∅ := by
  have h := Veles.{name}.T0.noExt
  simp only [Veles.{name}.T0.root, stateOf_nil, dec_zero] at h
  exact h

end Veles.{name}
""" + controls)
    print(f"{len(new)} trees (from {len(trees)}), largest {maxsz} branch nodes; modules in {mdir}")

if __name__ == "__main__":
    main()
