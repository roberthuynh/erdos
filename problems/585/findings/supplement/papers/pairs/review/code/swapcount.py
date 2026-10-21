# Convert an unlabeled list of connected bipartite graphs to the colour-preserving count used by genbg:
# a graph counts once if some automorphism swaps its two colour classes, twice otherwise.
import sys, networkx as nx
from networkx.algorithms import bipartite
tot = 0; noswap = 0; k = 0
for line in open(sys.argv[1]):
    s = line.strip()
    if not s or s.startswith(">"): continue
    G = nx.from_graph6_bytes(s.encode()); k += 1
    A, B = bipartite.sets(G)
    G1 = G.copy(); G2 = G.copy()
    for v in G: G1.nodes[v]["c"] = 0 if v in A else 1; G2.nodes[v]["c"] = 1 if v in A else 0
    sw = nx.is_isomorphic(G1, G2, node_match=lambda x, y: x["c"] == y["c"]) if len(A) == len(B) else False
    tot += 1 if sw else 2; noswap += 0 if sw else 1
print(sys.argv[1], "unlabeled", k, "without colour swap", noswap, "colour-preserving count", tot)
