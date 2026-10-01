#!/usr/bin/env python3
"""Independent verifier for gen_cert certificates (shares no code with gen_cert.c).

Checks, for every TREE j with root blocks S_j:
  * the root blocks are k-subsets of [v] whose (k-1)-subsets are pairwise distinct (a packing);
  * replaying the tree from the root state consumes exactly its nodes, where
      I T   : T is an uncovered (k-1)-subset; children = compatible blocks T+{x}, x ascending;
      R j p : p is a permutation of [v] and p(current covered set) == covered set of root j;
  * every R target is the root of a tree with strictly more root blocks than the root of the tree
    containing the R node, which makes the reference graph acyclic.
Tree 0 must have the requested start state. Prints a summary and the SHA-256 of the file.
Usage: verify_cert.py k v cert.txt [startfile|-] [preitemsfile]
TREE lines may end with "ITEMS i1 i2 ...": items covered from the start (the same for every tree)."""
import hashlib, sys

def main():
    k, v, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    start = []
    if len(sys.argv) > 4 and sys.argv[4] != "-":
        start = [int(x) for x in open(sys.argv[4]).read().split()]
    raw = open(path, "rb").read()
    lines = raw.decode().split("\n")
    trees, cur = {}, None
    for ln in lines:
        if not ln:
            continue
        f = ln.split()
        if f[0] == "TREE":
            j, nb = int(f[1]), int(f[2])
            blocks = [int(x) for x in f[3:3 + nb]]
            assert len(blocks) == nb, ln
            rest = f[3 + nb:]
            pre = []
            if rest:
                assert rest[0] == "ITEMS", ln
                pre = [int(x) for x in rest[1:]]
            assert j not in trees, f"duplicate tree {j}"
            cur = trees[j] = {"blocks": blocks, "pre": pre, "nodes": []}
        elif f[0] == "END":
            cur = None
        else:
            assert cur is not None, "node outside a tree"
            cur["nodes"].append(f)
    assert 0 in trees and sorted(trees) == list(range(len(trees))), "tree ids must be 0..n-1"
    assert sorted(trees[0]["blocks"]) == sorted(start), "tree 0 is not the start state"

    def subs(B):
        return [B & ~(1 << y) for y in range(v) if B >> y & 1]

    def cover_of(blocks, pre=()):
        cov = set()
        for T in pre:
            assert 0 <= T < (1 << v) and bin(T).count("1") == k - 1 and T not in cov, f"bad pre-covered item {T}"
            cov.add(T)
        for B in blocks:
            assert 0 <= B < (1 << v) and bin(B).count("1") == k, f"bad block {B}"
            S = subs(B)
            assert not (set(S) & cov), f"blocks overlap in a (k-1)-set: {B}"
            cov.update(S)
        return frozenset(cov)

    roots = {j: cover_of(t["blocks"], t["pre"]) for j, t in trees.items()}
    pre0 = sorted(trees[0]["pre"])
    assert all(sorted(t["pre"]) == pre0 for t in trees.values()), "trees disagree on pre-covered items"
    if len(sys.argv) > 5:
        want = sorted(int(x) for x in open(sys.argv[5]).read().split())
        assert pre0 == want, "pre-covered items differ from the requested file"
    nblocks = {j: len(t["blocks"]) for j, t in trees.items()}
    total_I = total_R = 0
    for j, t in trees.items():
        nodes, pos = t["nodes"], 0
        cov = set(roots[j])
        depth = [nblocks[j]]

        def node():
            nonlocal pos, total_I, total_R
            assert pos < len(nodes), f"tree {j}: stream ended"
            f = nodes[pos]; pos += 1
            if f[0] == "R":
                tgt = int(f[1]); p = [int(x) for x in f[2].split(",")]
                assert sorted(p) == list(range(v)), f"tree {j}: not a permutation"
                assert tgt in trees, f"tree {j}: unknown target {tgt}"
                assert nblocks[tgt] > nblocks[j], f"tree {j} -> {tgt}: reference not upward"
                assert nblocks[tgt] == depth[0], f"tree {j}: block count mismatch at R"
                img = frozenset(sum(1 << p[y] for y in range(v) if m >> y & 1) for m in cov)
                assert img == roots[tgt], f"tree {j}: permutation does not map state onto root {tgt}"
                total_R += 1
                return
            assert f[0] == "I", f"tree {j}: bad node {f}"
            T = int(f[1])
            assert 0 <= T < (1 << v) and bin(T).count("1") == k - 1 and T not in cov, f"tree {j}: bad item {T}"
            total_I += 1
            for x in range(v):
                if T >> x & 1:
                    continue
                S = subs(T | 1 << x)
                if any(s in cov for s in S):
                    continue
                cov.update(S); depth[0] += 1
                node()
                depth[0] -= 1; cov.difference_update(S)

        node()
        assert pos == len(nodes), f"tree {j}: {len(nodes) - pos} unread nodes"
    print(f"CERT PASS: {len(trees)} trees, {total_I} branch nodes, {total_R} reductions; "
          f"sha256 {hashlib.sha256(raw).hexdigest()}")

if __name__ == "__main__":
    sys.setrecursionlimit(1 << 20)
    try:
        main()
    except AssertionError as e:
        print(f"CERT FAIL: {e}"); sys.exit(1)
