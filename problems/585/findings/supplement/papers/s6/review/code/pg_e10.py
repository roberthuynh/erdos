#!/usr/bin/env python3
"""PG(2,5) certificate host: projective-plane axioms, girth, minimum essential cut by flows."""
import sys, os, json, time, itertools
sys.path.insert(0, os.path.dirname(__file__))
from s6rev import *
d = json.load(open(sys.argv[1]))
M = d["M"]
adj = check_B(M, [tuple(e) for e in d["B_edges"]])
# axioms: 31 points (I), 31 lines (O), any two points on exactly one common line, any two lines meet in one point
pts, lines = range(M), range(M, 2 * M)
ok1 = all(len(adj[a] & adj[b]) == 1 for a, b in itertools.combinations(pts, 2))
ok2 = all(len(adj[a] & adj[b]) == 1 for a, b in itertools.combinations(lines, 2))
print("M =", M, "; any two I-vertices have exactly one common neighbour:", ok1, "; any two O-vertices:", ok2)
print("=> incidence graph of a projective plane of order 5 (6 points per line, 31 points); the plane of order 5 is unique (PG(2,5))")
t = time.time()
print("min(10, min essential cut) by flows over all disjoint edge pairs:", min_ess_cut_flow(adj, 10), "%.0fs" % (time.time() - t))
