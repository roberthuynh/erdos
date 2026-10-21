# Independent check of Example 4 (R20). Independent of the author's code.
# Builds R20 from the PAPER's text, compares with data/rigid20.g6 (networkx parser),
# checks counts, degrees, the (5,1) set, the K_{4,4} pair, and writes an edge list for the C checks.
import sys, itertools
import networkx as nx

HERE = sys.argv[1]  # path to census/pairs-lane
TP, WP, TQ, WQ = range(0,5), range(5,10), range(10,15), range(15,20)
G = nx.Graph()
G.add_nodes_from(range(20))
for p in TP:
    for q in TQ: G.add_edge(p, q)
for p in WP:
    for q in WQ: G.add_edge(p, q)
for i in range(5): G.add_edge(i, 15+i)
G.add_edge(10, 5)

F = nx.read_graph6(HERE + "/data/rigid20.g6")
print("file graph: n=%d e=%d" % (F.number_of_nodes(), F.number_of_edges()))
print("text graph: n=%d e=%d" % (G.number_of_nodes(), G.number_of_edges()))
print("isomorphic:", nx.is_isomorphic(F, G))
print("identical labels:", set(map(frozenset, F.edges())) == set(map(frozenset, G.edges())))
P = set(range(10)); Q = set(range(10,20))
assert all((u in P) != (v in P) for u, v in G.edges())
print("bipartite with P=0..9, Q=10..19: True")
degs = sorted(d for _, d in G.degree())
from collections import Counter
print("degree multiset:", dict(Counter(degs)), "max", max(degs), "3n-4 =", 3*20-4)
def D(Z): return sum(6 - G.degree(v) for v in Z)
print("D(P)=%d D(Q)=%d" % (D(P), D(Q)))
T = set(TP) | set(TQ)
dQ = sum(1 for q in TQ for p in G[q] if p not in T)
dP = sum(1 for p in TP for q in G[p] if q not in T)
eT = G.subgraph(T).number_of_edges(); eW = G.subgraph(set(range(20)) - T).number_of_edges()
print("dQ(T)=%d dP(T)=%d D(TQ)=%d D(TP)=%d D(P-T)=%d D(Q-T)=%d g(T)=%d g(V-T)=%d" % (
    dQ, dP, D(TQ), D(TP), D(WP), D(WQ), 6*10-2*eT, 6*10-2*eW))
# the pair
c1 = [0,10,1,11,2,12,3,13]; c2 = [0,11,3,10,2,13,1,12]
def cyc_edges(c): return {frozenset((c[i], c[(i+1) % len(c)])) for i in range(len(c))}
E1, E2 = cyc_edges(c1), cyc_edges(c2)
ok = (len(set(c1)) == 8 and set(c1) == set(c2) and len(E1) == 8 and len(E2) == 8
      and not (E1 & E2) and all(G.has_edge(*tuple(e)) for e in E1 | E2))
print("pair (two 8-cycles on {0,1,2,3,10,11,12,13}, edge-disjoint, edges in G):", ok)
with open(sys.argv[2], "w") as f:
    f.write("%d %d\n" % (20, G.number_of_edges()))
    for u, v in sorted(G.edges()): f.write("%d %d\n" % (u, v))
