# Random "two-block" E4 instances on t+t | t+t vertices (P = 0..2t-1, Q = 2t..4t-1), blocks T and W
# dense, crossing edges with dQ(T) = 2 (or 3) and dP(T) chosen so the instance is E4. Prints graph6.
import sys, random, itertools
import networkx as nx
t = int(sys.argv[1]); N = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
a = 2 * t; n = 4 * t
TP = list(range(0, t)); WP = list(range(t, a)); TQ = list(range(a, a + t)); WQ = list(range(a + t, n))
out = set(); tries = 0
while len(out) < N and tries < 200000:
    tries += 1
    G = nx.Graph(); G.add_nodes_from(range(n))
    # blocks: complete bipartite minus a few random edges
    for BP, BQ in ((TP, TQ), (WP, WQ)):
        es = [(p, q) for p in BP for q in BQ]
        drop = rng.randint(0, 2 * t)
        rng.shuffle(es)
        G.add_edges_from(es[drop:])
    dq = rng.choice([2, 2, 3]); dp = rng.randint(3, 6)
    for _ in range(dq):
        G.add_edge(rng.choice(TQ), rng.choice(WP))
    for _ in range(dp):
        G.add_edge(rng.choice(TP), rng.choice(WQ))
    if max(d for _, d in G.degree()) > 6 or min(d for _, d in G.degree()) < 4: continue
    if G.number_of_edges() != 3 * n - 4: continue
    if sum(6 - G.degree(v) for v in range(a)) != 4: continue
    out.add(nx.to_graph6_bytes(G, header=False).decode().strip())
for s in out: print(s)
print("tries", tries, "instances", len(out), file=sys.stderr)
