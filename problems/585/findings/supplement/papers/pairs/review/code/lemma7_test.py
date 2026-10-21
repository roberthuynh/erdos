# Empirical test of PAPER Lemma 7 (and its Remark) with an independent code.
# Input: graph6 list of E4 instances, colour classes P = 0..a-1, Q = a..2a-1 (genbg order).
# For each graph: a 4-factor by max flow, then random alternating-cycle swaps; every 2-edge cut T of
# every sampled 4-factor F (both sides) is tested against Lemma 7 (a)/(b), per H-edge q->p.
import sys, random, itertools
import networkx as nx
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
LIMIT = int(sys.argv[2])
def four_factor(G, P, Q):
    D = nx.DiGraph()
    for p in P: D.add_edge("s", p, capacity=4)
    for q in Q: D.add_edge(q, "t", capacity=4)
    for p in P:
        for q in G[p]: D.add_edge(p, q, capacity=1)
    val, flow = nx.maximum_flow(D, "s", "t")
    if val != 4 * len(P): return None
    return {frozenset((p, q)) for p in P for q in G[p] if flow[p][q] == 1}
def digraph(G, F, P):
    A = {v: set() for v in G}
    for u, w in G.edges():
        p, q = (u, w) if u in P else (w, u)
        if frozenset((p, q)) in F: A[p].add(q)
        else: A[q].add(p)
    return A
def reach(A, s, banned):
    seen = {s}; st = [s]; par = {s: None}
    while st:
        x = st.pop()
        for y in A[x]:
            if (x, y) in banned or y in seen: continue
            seen.add(y); par[y] = x; st.append(y)
    return seen, par
def random_swap(G, F, P):
    A = digraph(G, F, P)
    # random walk until a vertex repeats; the loop is a directed cycle
    v = rng.choice(list(G)); path = [v]; pos = {v: 0}
    for _ in range(4 * len(G)):
        if not A[v]: return F
        w = rng.choice(sorted(A[v]))
        if w in pos:
            cyc = path[pos[w]:] + [w]
            E = {frozenset((cyc[i], cyc[i + 1])) for i in range(len(cyc) - 1)}
            return F ^ E
        pos[w] = len(path); path.append(w); v = w
    return F
def two_cuts(G, F):
    H = nx.Graph(); H.add_nodes_from(G); H.add_edges_from(tuple(e) for e in F)
    if not nx.is_connected(H): return []
    out = []
    El = sorted(tuple(sorted(e)) for e in F)
    for e, f in itertools.combinations(El, 2):
        H.remove_edge(*e); H.remove_edge(*f)
        if not nx.is_connected(H):
            comp = nx.node_connected_component(H, e[0])
            out.append(frozenset(comp)); out.append(frozenset(set(G) - comp))
        H.add_edge(*e); H.add_edge(*f)
    return list(set(out))
stats = dict(cuts=0, hedges=0, case_a_edges=0, case_b_edges=0, a_ok=0, b_ok=0, eps0=0, eps0_dxp0=0, remark_ok=0, fail=0, thin=0)
def check(G, F, T, P, Q, deg):
    stats["cuts"] += 1
    TP = T & P; TQ = T & Q
    assert len(TP) == len(TQ)
    cut = [e for e in F if len(e & T) == 1]
    assert len(cut) == 2
    e1 = [e for e in cut if (e & TP)][0]; e2 = [e for e in cut if (e & TQ)][0]
    p1 = next(iter(e1 & TP)); qprime = next(iter(e1 - TP)); q1 = next(iter(e2 & TQ)); pprime = next(iter(e2 - TQ))
    A = digraph(G, F, P)
    banned = {(p1, qprime), (pprime, q1)}
    Hedges = [(q, p) for q in TQ for p in G[q] if p not in T and frozenset((p, q)) not in F]
    if not Hedges: stats["thin"] += 1
    Dd = lambda Z: sum(6 - deg[v] for v in Z)
    for q, p in Hedges:
        stats["hedges"] += 1
        X, par = reach(A, p, banned)
        if q in X:
            stats["case_a_edges"] += 1
            path = [q]
            while path[-1] != p: path.append(par[path[-1]])
            path.reverse()  # p ... q
            cyc = path + [p]
            E = {frozenset((cyc[i], cyc[i + 1])) for i in range(len(cyc) - 1)}
            F2 = F ^ E
            okreg = all(sum(1 for e in F2 if v in e) == 4 for v in G)
            bd = sum(1 for e in F2 if len(e & T) == 1)
            if okreg and bd >= 4: stats["a_ok"] += 1
            else: stats["fail"] += 1; print("FAIL (a)", okreg, bd)
        else:
            stats["case_b_edges"] += 1
            XP = X & P; XQ = X & Q; j = len(XQ) - len(XP)
            eps = sum(1 for e in (e1, e2) if (e & P) <= X and not ((e & Q) <= X))
            eX = sum(1 for u, w in G.edges() if u in X and w in X)
            gX = 6 * len(X) - 2 * eX
            eH_out = sum(1 for x in XP for y in G[x] if y not in X and frozenset((x, y)) not in F)
            Fnb = sum(1 for y in G[p] if frozenset((p, y)) in F and y in X)
            conds = [gX == 2 * j + 2 * eps + 2 * Dd(XQ), eH_out == Dd(XQ) - Dd(XP) - 2 * j,
                     3 * Dd(XQ) >= 11 - 2 * eps + Dd(XP), Dd(XQ) >= 3, gX >= 10, Fnb >= 3, eps in (0, 1, 2)]
            if eps == 0:
                stats["eps0"] += 1
                conds += [Dd(XQ) == 4, Dd(XP) <= 1, j == 1]
                if Dd(XP) == 0:
                    stats["eps0_dxp0"] += 1
                    dP = sum(1 for x in XP for y in G[x] if y not in X)
                    dQ = sum(1 for x in XQ for y in G[x] if y not in X)
                    rem = (gX == 10 and dP == 2 and dQ == 4)
                    conds.append(rem)
                    if rem: stats["remark_ok"] += 1
            if all(conds): stats["b_ok"] += 1
            else: stats["fail"] += 1; print("FAIL (b)", conds, eps, j, Dd(XQ), Dd(XP))
ng = 0
for line in open(sys.argv[1]):
    s = line.split()[0] if line.strip() else ""
    if not s: continue
    G = nx.from_graph6_bytes(s.encode()); n = G.number_of_nodes(); a = n // 2
    P = set(range(a)); Q = set(range(a, n)); deg = dict(G.degree())
    if sum(6 - deg[v] for v in P) != 4 or sum(6 - deg[v] for v in Q) != 4: continue
    F = four_factor(G, sorted(P), sorted(Q))
    if F is None: continue
    for it in range(30):
        F = random_swap(G, F, P)
        for T in two_cuts(G, F): check(G, F, T, P, Q, deg)
    ng += 1
    if ng >= LIMIT: break
print("graphs", ng, stats)
