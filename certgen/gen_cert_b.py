#!/usr/bin/env python3
"""Second, independent implementation of the certificate generator (shares no code with
gen_cert.c; written from the specification below). Its output must be byte-identical to
gen_cert.c's on the same inputs (compare SHA-256).

Specification (the determinism both implementations follow):
- Items: (k-1)-subsets of [v], named by point mask; scanned in increasing mask order.
- Phases P_0..P_{r-1} (point masks): the current phase of a state is the first p with an uncovered
  item containing P_p, else r (free).
- Branching item: among uncovered items of the current phase (all uncovered items when free), the
  one with the fewest compatible blocks T+{x}; ties: the smallest mask; a zero stops the scan.
- Children: x ascending among points outside T whose block has all (k-1)-subsets uncovered.
- Sibling pruning: in phases < DP, while (blocks - phase start - 1) < D after placing the child
  block, the child state is compared with the kept siblings (in order) by the isomorphism search;
  the first hit gives "R j perm"; otherwise the child becomes a new tree (reduced by identity).
- Classification: at a non-root node whose phase index exceeds its parent's (and the parent's is
  < r), compare with every tree representing the parent's phase (in id order); first hit gives
  "R j perm", else a new representative tree (phase start = current block count).
- Isomorphism search from A to B (as item sets): counts equal and sorted degree lists equal, else
  fail; points ordered by degree with the selection swap "for a < b: if deg[o[b]] > deg[o[a]]
  swap"; recursion over positions: step count +1 per call after the success test, fail beyond
  2,000,000 steps; a degree-0 point maps it and all later points, in order, to the smallest unused
  degree-0 targets; otherwise targets z ascending, unused, same degree; after assigning, every item
  of A whose last point (in assignment order) is this point must map into B.
- Trees are processed in id order; output format as gen_cert.c.
Usage: gen_cert_b.py k v D DP phasefile startfile  (env START_ITEMS as for gen_cert.c)
"""
import os, sys
import numpy as np
sys.setrecursionlimit(1 << 20)

def main():
    K, V, D, DP = (int(a) for a in sys.argv[1:5])
    phases = [int(x) for x in open(sys.argv[5]).read().split()]
    NPH = len(phases)
    items = [m for m in range(1 << V) if bin(m).count("1") == K - 1]
    pts = list(range(V))
    out = []
    DUMMY = 1 << V
    covered = np.zeros(DUMMY + 1, dtype=np.uint8); covered[DUMMY] = 1
    IT = np.array(items, dtype=np.int64)
    SUB = np.full((len(items), V, K), DUMMY, dtype=np.int64)   # subsets of item+{x}
    for i, m in enumerate(items):
        for x in range(V):
            if m >> x & 1: continue
            B = m | 1 << x
            SUB[i, x, :] = [B & ~(1 << y) for y in range(V) if B >> y & 1]
    PH_OK = [np.array([(m & P) == P for m in items]) for P in phases]
    PH_IDX = [IT[ok] for ok in PH_OK]
    blocks = []
    start_items = []
    if os.environ.get("START_ITEMS"):
        for t in open(os.environ["START_ITEMS"]).read().split():
            t = int(t)
            assert bin(t).count("1") == K - 1 and not covered[t]
            covered[t] = 1; start_items.append(t)
    if sys.argv[6] != "-":
        for b in open(sys.argv[6]).read().split():
            b = int(b)
            subs = [b & ~(1 << y) for y in pts if b >> y & 1]
            assert bin(b).count("1") == K and not any(covered[s] for s in subs)
            for s in subs: covered[s] = 1
            blocks.append(b)

    def subs(B):
        return [B & ~(1 << y) for y in pts if B >> y & 1]

    def compat(cov, B):
        for s in subs(B):
            if cov[s]: return False
        return True

    def cur_phase(cov):
        for p in range(NPH):
            if not cov[PH_IDX[p]].all():
                return p
        return NPH

    roots = []            # (covered bytes, blocks list)
    rep_of, start_of = [], []

    def new_tree(cov, bl, rep, st):
        roots.append((cov.copy(), list(bl))); rep_of.append(rep); start_of.append(st)
        return len(roots) - 1

    budget = 2000000

    def find_iso(A, Bc):
        degA = [0] * V; degB = [0] * V; itA = []; cA = cB = 0
        for m in items:
            if A[m]:
                itA.append(m); cA += 1
                for y in pts:
                    if m >> y & 1: degA[y] += 1
            if Bc[m]:
                cB += 1
                for y in pts:
                    if m >> y & 1: degB[y] += 1
        if cA != cB or sorted(degA) != sorted(degB):
            return None
        order = list(range(V))
        for a in range(V):
            for b in range(a + 1, V):
                if degA[order[b]] > degA[order[a]]:
                    order[a], order[b] = order[b], order[a]
        pos = [0] * V
        for i, y in enumerate(order): pos[y] = i
        by_last = [[] for _ in range(V)]
        for m in itA:
            by_last[max(pos[y] for y in pts if m >> y & 1)].append(m)
        perm = [0] * V; used = [False] * V; steps = [0]

        def img(m):
            r = 0
            for y in pts:
                if m >> y & 1: r |= 1 << perm[y]
            return r

        def rec(i):
            if i == V: return True
            steps[0] += 1
            if steps[0] > budget: return False
            y = order[i]
            if degA[y] == 0:
                for r in range(i, V):
                    z = 0
                    while used[z] or degB[z] != 0: z += 1
                    perm[order[r]] = z; used[z] = True
                return True
            for z in pts:
                if used[z] or degA[y] != degB[z]: continue
                perm[y] = z; used[z] = True
                if all(Bc[img(m)] for m in by_last[i]) and rec(i + 1):
                    return True
                used[z] = False
            return False

        return list(perm) if rec(0) else None

    ident = list(pts)

    def emit_r(j, p):
        out.append("R %d %s" % (j, ",".join(map(str, p))))

    nodes = [0]
    def search(cov, bl, st, last, is_root):
        ph = cur_phase(cov)
        if not is_root and ph > last and ph <= NPH and last < NPH:
            for j in range(len(roots)):
                if rep_of[j] == last:
                    p = find_iso(cov, roots[j][0])
                    if p is not None:
                        emit_r(j, p); return
            j = new_tree(cov, bl, last, len(bl)); emit_r(j, ident); return
        counts = (cov[SUB].max(axis=2) == 0).sum(axis=1)
        elig = cov[IT] == 0
        if ph < NPH: elig &= PH_OK[ph]
        best = -1
        if elig.any():
            best = items[int(np.argmin(np.where(elig, counts, 1 << 30)))]
        if best < 0:
            raise SystemExit("SOLUTION FOUND")
        nodes[0] += 1
        out.append("I %d" % best)
        kept = []
        for x in pts:
            if best >> x & 1: continue
            B = best | 1 << x
            if not compat(cov, B): continue
            S = subs(B)
            for s in S: cov[s] = 1
            bl.append(B)
            if ph < DP and len(bl) - 1 - st < D:
                hit = None
                for q in kept:
                    p = find_iso(cov, roots[q][0])
                    if p is not None:
                        hit = (q, p); break
                if hit: emit_r(*hit)
                else:
                    j = new_tree(cov, bl, -1, st); kept.append(j); emit_r(j, ident)
            else:
                search(cov, bl, st, ph, False)
            bl.pop()
            for s in S: cov[s] = 0

    new_tree(covered, blocks, -1, 0)
    done = 0
    with open(sys.stdout.fileno(), "w", closefd=False) as fh:
        while done < len(roots):
            j = done; done += 1
            cov = roots[j][0].copy(); bl = list(roots[j][1])
            line = "TREE %d %d" % (j, len(bl)) + "".join(" %d" % b for b in bl)
            if start_items: line += " ITEMS" + "".join(" %d" % t for t in start_items)
            out.clear(); out.append(line)
            search(cov, bl, start_of[j], cur_phase(cov), True)
            out.append("END")
            fh.write("\n".join(out) + "\n")
    print(f"TOTAL nodes={nodes[0]} trees={len(roots)}", file=sys.stderr)

if __name__ == "__main__":
    main()
