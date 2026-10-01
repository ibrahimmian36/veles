#!/usr/bin/env python3
"""Check the phase representatives of the S(4,5,15) certificate (certs/cert15.txt.xz).

The trees whose roots have 26 blocks contain the blocks through {13, 14}; removing 13 and 14 must
give a Steiner triple system of order 13. The trees whose roots have 91 blocks contain the blocks
through 14; removing 14 must give an S(3,4,14). The script checks both, and checks that the
systems of each kind are pairwise non-isomorphic: Pasch counts for the triple systems, and the
sorted multiset, over pairs of disjoint blocks, of the number of blocks inside their union for the S(3,4,14) (an isomorphism
invariant; distinct multisets imply non-isomorphic). Exit 0 when there are exactly two and four,
pairwise non-isomorphic. Usage: check_reps.py"""
import itertools, lzma, os, sys
from collections import Counter
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def trees():
    for ln in lzma.open(os.path.join(ROOT, "certs/cert15.txt.xz"), "rt"):
        f = ln.split()
        if f and f[0] == "TREE":
            yield [int(x) for x in f[3:3 + int(f[2])]]

def pts(m): return frozenset(i for i in range(15) if m >> i & 1)

def is_steiner(blocks, t, v):
    seen = Counter()
    for B in blocks:
        for T in itertools.combinations(sorted(B), t): seen[T] += 1
    return all(seen[T] == 1 for T in itertools.combinations(range(v), t))

def pasch(trip):
    s = [set(b) for b in trip]
    return sum(1 for q in itertools.combinations(range(len(s)), 4) if len(set().union(*(s[i] for i in q))) == 6)

def union_profile(blocks):
    """For each pair of disjoint blocks, the number of blocks inside their 8-point union."""
    return tuple(sorted(Counter(sum(1 for c in blocks if c <= (a | b))
                                for a, b in itertools.combinations(blocks, 2) if not (a & b)).items()))

sts, sqs = [], []
for bl in trees():
    B = [pts(m) for m in bl]
    if len(bl) == 26 and all({13, 14} <= b for b in B):
        sts.append([b - {13, 14} for b in B])
    elif len(bl) == 91 and all(14 in b for b in B):
        sqs.append([b - {14} for b in B])
ok = len(sts) == 2 and len(sqs) == 4
ok &= all(is_steiner(s, 2, 13) for s in sts) and all(is_steiner(s, 3, 14) for s in sqs)
p = [pasch(s) for s in sts]; u = [union_profile(s) for s in sqs]
ok &= len(set(p)) == 2 and len(set(u)) == 4
print(f"STS(13) representatives: {len(sts)}, Pasch counts {sorted(p)}; S(3,4,14) representatives: "
      f"{len(sqs)}, {len(set(u))} distinct union profiles")
print("REPS:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
