# Check that the graphs in a g6 file (rows 0..R-1, columns R..) are pairwise non-isomorphic under
# colour-preserving isomorphism, and count classes when the colour classes may be swapped.
import sys, networkx as nx
R = int(sys.argv[2])
gs = [nx.from_graph6_bytes(l.strip().encode()) for l in open(sys.argv[1]) if l.strip()]
for G in gs:
    for v in G: G.nodes[v]["side"] = 0 if v < R else 1
nm = lambda a, b: a["side"] == b["side"]
dup = 0
for i in range(len(gs)):
    for j in range(i):
        if nx.is_isomorphic(gs[i], gs[j], node_match=nm): dup += 1
reps = []
for G in gs:
    if not any(nx.is_isomorphic(G, H) for H in reps): reps.append(G)
print(sys.argv[1], "graphs", len(gs), "colour-preserving duplicates", dup, "classes allowing swap", len(reps))
