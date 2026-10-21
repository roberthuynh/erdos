# Validate rpair against networkx.simple_cycles on known and random graphs.
import sys, random, subprocess, itertools
import networkx as nx
RP = sys.argv[1]
def g6(G):
    return nx.to_graph6_bytes(nx.convert_node_labels_to_integers(G), header=False).decode().strip()
def py_pair(G):
    cyc = list(nx.simple_cycles(G))
    groups = {}
    for c in cyc:
        vs = frozenset(c); es = frozenset(frozenset((c[i], c[(i+1) % len(c)])) for i in range(len(c)))
        groups.setdefault(vs, []).append(es)
    for vs, L in groups.items():
        for a, b in itertools.combinations(L, 2):
            if not (a & b): return True, len(cyc)
    return False, len(cyc)
known = {"K4": nx.complete_graph(4), "K5": nx.complete_graph(5), "K33": nx.complete_bipartite_graph(3,3),
         "K44": nx.complete_bipartite_graph(4,4), "oct": nx.complete_multipartite_graph(2,2,2),
         "bowtie": nx.from_edgelist([(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
         "K44-pm": nx.complete_bipartite_graph(4,4)}
known["K44-pm"].remove_edges_from([(i, 4+i) for i in range(4)])
tests = list(known.items())
rng = random.Random(585)
for t in range(400):
    nv = rng.randint(4, 10); p = rng.choice([0.4, 0.5, 0.6, 0.7])
    G = nx.gnp_random_graph(nv, p, seed=rng.randint(0, 10**9))
    if G.number_of_edges() > 0: tests.append(("rand%d" % t, G))
inp = "\n".join(g6(G) for _, G in tests) + "\n"
out = subprocess.run([RP, "f"], input=inp, capture_output=True, text=True).stdout.split("\n")
bad = 0; npair = 0
for (name, G), line in zip(tests, out):
    f = line.split()
    mine = (f[1] == "PAIR", int(f[2]))
    ref = py_pair(G)
    if mine != ref:
        bad += 1; print("MISMATCH", name, mine, ref)
    npair += ref[0]
    if not name.startswith("rand"): print(name, mine, ref)
print("tested", len(tests), "mismatches", bad, "with pairs", npair)
