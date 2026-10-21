# Are the six T1 instances distinct up to isomorphism (plain Y, marked Y, X with v marked, Z)?
import sys, itertools
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
inst = []
for line in open(sys.argv[1]):
    f = line.split(); Y = nx.from_graph6_bytes(f[0].encode()); a, b, c, d = map(int, f[1:5])
    M = Y.copy()
    for u, w in M.edges(): M[u][w]["mark"] = 1 if {u, w} in ({a, b}, {c, d}) else 0
    Z = Y.copy(); Z.remove_edge(a, b); Z.remove_edge(c, d)
    inst.append((Y, M, Z))
em = lambda x, y: x["mark"] == y["mark"]
def classes(graphs, edge_match=None):
    reps = []
    lab = []
    for G in graphs:
        for i, R in enumerate(reps):
            if nx.is_isomorphic(G, R, edge_match=edge_match): lab.append(i); break
        else: reps.append(G); lab.append(len(reps) - 1)
    return lab
print("Y classes:", classes([t[0] for t in inst]))
print("marked Y classes:", classes([t[1] for t in inst], em))
print("Z classes:", classes([t[2] for t in inst]))
for i, (Y, M, Z) in enumerate(inst):
    core = nx.k_core(Z, 4)
    print(i, "Z: n=%d e=%d maxdeg=%d mindeg=%d; 4-core n=%d e=%d; degree seq Y %s" % (
        Z.number_of_nodes(), Z.number_of_edges(), max(d for _, d in Z.degree()), min(d for _, d in Z.degree()),
        core.number_of_nodes(), core.number_of_edges(), sorted((d for _, d in Y.degree()), reverse=True)))
