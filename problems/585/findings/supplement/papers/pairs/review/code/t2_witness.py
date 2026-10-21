# For each line "X v a v c v d NONE" of the author's data/t2_none.txt: search (own code, networkx cycles)
# for a pair of X with C1 through v-a and v-b (b = the 4th neighbour) and C2 through v-c and v-d.
# Print the witness and re-verify it edge by edge.
import sys, collections, itertools
import networkx as nx
out = []
nwit = 0; nnone = 0
for line in open(sys.argv[1]):
    t = line.split()
    X = nx.from_graph6_bytes(t[0].encode()); v = int(t[1]); a, c, d = int(t[2]), int(t[4]), int(t[6])
    b = [u for u in X[v] if u not in (a, c, d)][0]
    by = collections.defaultdict(list)
    for cyc in nx.simple_cycles(X):
        if v not in cyc: continue
        es = frozenset(frozenset((cyc[i], cyc[(i + 1) % len(cyc)])) for i in range(len(cyc)))
        by[frozenset(cyc)].append((cyc, es))
    va, vb, vc, vd = (frozenset((v, x)) for x in (a, b, c, d))
    wit = None
    for S, L in by.items():
        A = [x for x in L if va in x[1] and vb in x[1]]
        B = [x for x in L if vc in x[1] and vd in x[1]]
        for x in A:
            for y in B:
                if not (x[1] & y[1]): wit = (x, y); break
            if wit: break
        if wit: break
    if wit:
        (c1, e1), (c2, e2) = wit
        ok = (set(c1) == set(c2) and len(set(c1)) == len(c1) and len(set(c2)) == len(c2) and not (e1 & e2)
              and all(X.has_edge(*tuple(e)) for e in e1 | e2) and len(e1) == len(c1) and len(e2) == len(c2))
        nwit += 1
        print(t[0], v, "pairing {%d%d|%d%d} REALISED" % (a, b, c, d), "C1=" + ",".join(map(str, c1)), "C2=" + ",".join(map(str, c2)), "verified=%s" % ok)
    else:
        nnone += 1
        print(t[0], v, "pairing {%d%d|%d%d} NOT REALISED" % (a, b, c, d))
print("lines", nwit + nnone, "witness found", nwit, "confirmed not realised", nnone, file=sys.stderr)
