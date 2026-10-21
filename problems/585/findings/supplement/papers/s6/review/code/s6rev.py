#!/usr/bin/env python3
"""Independent code for papers/s6/PAPER.md. Written from the paper's definitions only; shares no code
with s6/code/.

Conventions. B has vertices 0..2M-1, I = 0..M-1, O = M..2M-1; o in I, y in O, oy an edge.
Y = B - o - y, P = O - y and Q = I - o, both indexed 0..m-1 (m = M - 1).
A frame is six perfect matchings of Y+ = Y + Lambda (colours 0..5) with Lambda in colours 4, 5.
Matching c is stored as mp[c][p] = q and lam[c][p] = 1 iff the colour-c edge at p is a Lambda edge.
Phi = c(N0 u N1) + c(N2 u N3).
"""
import sys, json, random, itertools
from collections import deque


# ---------------------------------------------------------------- host graph checks

def check_B(M, edges):
    """B simple, bipartite with I = 0..M-1 / O = M..2M-1, 6-regular. Returns adjacency sets."""
    n = 2 * M
    adj = [set() for _ in range(n)]
    for a, b in edges:
        u, v = min(a, b), max(a, b)
        if not (0 <= u < M <= v < n):
            raise ValueError("edge not between I and O: %r" % ((a, b),))
        if v in adj[u]:
            raise ValueError("repeated edge %r" % ((u, v),))
        adj[u].add(v)
        adj[v].add(u)
    if any(len(adj[v]) != 6 for v in range(n)):
        raise ValueError("not 6-regular")
    return adj


def min_ess_cut_brute(adj):
    """Exact minimum of |d(S)| over S with 2 <= |S| <= n-2, by enumerating every S avoiding the
    last vertex (each bipartition has exactly one such side). Gray code, incremental cut size."""
    n = len(adj)
    nb = [0] * n
    for v in range(n):
        for w in adj[v]:
            nb[v] |= 1 << w
    best = None
    S = 0
    cut = 0
    size = 0
    N = n - 1  # vertices 0..n-2 may be in S
    for i in range(1, 1 << N):
        v = (i & -i).bit_length() - 1  # bit flipped in Gray code step i
        inS = (S >> v) & 1
        k = bin(nb[v] & S).count("1")
        if inS:
            S &= ~(1 << v)
            cut += -len(adj[v]) + 2 * k
            size -= 1
        else:
            cut += len(adj[v]) - 2 * k
            S |= 1 << v
            size += 1
        if 2 <= size <= n - 2:
            if best is None or cut < best:
                best = cut
    return best


def _maxflow_sets(adj, S, T, cap):
    """Undirected unit-capacity max flow between vertex sets S and T, stopped at cap."""
    flow = {}
    total = 0
    Sset, Tset = set(S), set(T)
    while total < cap:
        par = {s: None for s in Sset}
        dq = deque(Sset)
        hit = None
        while dq and hit is None:
            u = dq.popleft()
            for v in adj[u]:
                if v in par:
                    continue
                if flow.get((u, v), 0) < 1:
                    par[v] = u
                    if v in Tset:
                        hit = v
                        break
                    dq.append(v)
        if hit is None:
            break
        v = hit
        while par[v] is not None:
            u = par[v]
            flow[(u, v)] = flow.get((u, v), 0) + 1
            flow[(v, u)] = flow.get((v, u), 0) - 1
            v = u
        total += 1
    return total


def min_ess_cut_flow(adj, cap=10):
    """min(cap, minimum essential edge cut). Valid for cap <= 11 in a 6-regular graph: a cut S
    with |d(S)| < 12 and both sides >= 2 can be shrunk to one whose two sides each contain an
    edge (a side all of whose components are single vertices has |d| = 6|side| >= 12), so the
    minimum is attained between two disjoint edges with ends contracted."""
    n = len(adj)
    E = sorted({(min(u, v), max(u, v)) for u in range(n) for v in adj[u]})
    best = cap
    for i in range(len(E)):
        a = E[i]
        for j in range(i + 1, len(E)):
            b = E[j]
            if a[0] in b or a[1] in b:
                continue
            f = _maxflow_sets(adj, a, b, best)
            if f < best:
                best = f
    return best


# ---------------------------------------------------------------- instance and frames

class Inst:
    def __init__(self, M, Bedges, o, y):
        self.M = M
        self.adj = check_B(M, Bedges)
        if not (o < M <= y and y in self.adj[o]):
            raise ValueError("oy must be an edge with o in I, y in O")
        self.o, self.y = o, y
        self.Pl = [v for v in range(M, 2 * M) if v != y]
        self.Ql = [v for v in range(M) if v != o]
        self.m = M - 1
        self.pidx = {v: i for i, v in enumerate(self.Pl)}
        self.qidx = {v: i for i, v in enumerate(self.Ql)}
        self.Po = sorted(self.pidx[v] for v in self.adj[o] if v != y)
        self.Qy = sorted(self.qidx[v] for v in self.adj[y] if v != o)
        assert len(self.Po) == 5 and len(self.Qy) == 5
        self.Yedges = set()
        for pl in self.Pl:
            for ql in self.adj[pl]:
                if ql != o:
                    self.Yedges.add((self.pidx[pl], self.qidx[ql]))
        assert len(self.Yedges) == 6 * self.m - 5


def inv(a):
    r = [0] * len(a)
    for p, q in enumerate(a):
        r[q] = p
    return r


def ncyc(a, b):
    """number of cycles of N_a u N_b, given as mate arrays P -> Q"""
    ib = inv(b)
    m = len(a)
    seen = [False] * m
    c = 0
    for p in range(m):
        if not seen[p]:
            c += 1
            x = p
            while not seen[x]:
                seen[x] = True
                x = ib[a[x]]
    return c


def phi(F):
    mp = F[0]
    return ncyc(mp[0], mp[1]) + ncyc(mp[2], mp[3])


def check_frame(inst, F):
    """Full frame check: six perfect matchings, Lambda only in colours 4, 5, the colour classes
    partition E(Y) + Lambda with Lambda a perfect matching between P_o and Q_y."""
    mp, lam = F
    m = inst.m
    Ycount = {}
    L = []
    for c in range(6):
        if sorted(mp[c]) != list(range(m)):
            return "colour %d is not a perfect matching" % c
        for p in range(m):
            if lam[c][p]:
                if c < 4:
                    return "Lambda edge in colour %d" % c
                L.append((p, mp[c][p]))
            else:
                e = (p, mp[c][p])
                if e not in inst.Yedges:
                    return "non-edge %r in colour %d" % (e, c)
                Ycount[e] = Ycount.get(e, 0) + 1
    if set(Ycount) != inst.Yedges or any(v != 1 for v in Ycount.values()):
        return "Y edges not covered exactly once"
    if sorted(p for p, q in L) != inst.Po or sorted(q for p, q in L) != inst.Qy:
        return "Lambda is not a perfect matching P_o -> Q_y"
    return None


def copyF(F):
    return ([list(a) for a in F[0]], [list(a) for a in F[1]])


def key(F):
    mp, lam = F
    m = len(mp[0])
    k = [bytes(mp[c][p] + (m if lam[c][p] else 0) for p in range(m)) for c in range(6)]
    a = tuple(sorted((k[0], k[1])))
    b = tuple(sorted((k[2], k[3])))
    return (tuple(sorted((a, b))), tuple(sorted((k[4], k[5]))))


PAIRS = [(i, k) for i in range(6) for k in range(i + 1, 6)]


def kempe_components(F, i, k):
    """components of N_i u N_k as lists of P-vertices"""
    mp = F[0]
    ik = inv(mp[k])
    m = len(mp[0])
    seen = [False] * m
    comps = []
    for p in range(m):
        if not seen[p]:
            Z = []
            x = p
            while not seen[x]:
                seen[x] = True
                Z.append(x)
                x = ik[mp[i][x]]
            comps.append(Z)
    return comps


def legal(F, i, k, Z):
    if i >= 4 and k >= 4:
        return True
    lam = F[1]
    return not any(lam[i][x] or lam[k][x] for x in Z)


def swap(F, i, k, Z):
    G = copyF(F)
    mp, lam = G
    for x in Z:
        mp[i][x], mp[k][x] = mp[k][x], mp[i][x]
        lam[i][x], lam[k][x] = lam[k][x], lam[i][x]
    return G


def kempe_moves(F):
    out = []
    for i, k in PAIRS:
        for Z in kempe_components(F, i, k):
            if legal(F, i, k, Z):
                out.append(((("K", i, k, min(Z), len(Z))), swap(F, i, k, Z)))
    return out


def repairings(F):
    mp, lam = F
    out = []
    for order, name in (((0, 2, 1, 3), "R02|13"), ((0, 3, 1, 2), "R03|12")):
        G = ([list(mp[c]) for c in order] + [list(mp[4]), list(mp[5])],
             [list(lam[c]) for c in order] + [list(lam[4]), list(lam[5])])
        out.append(((name,), G))
    return out


def lambda_repairings(F):
    mp, lam = F
    out = []
    for k in (4, 5):
        L = [x for x in range(len(mp[k])) if lam[k][x]]
        for a, b in itertools.combinations(L, 2):
            G = copyF(F)
            G[0][k][a], G[0][k][b] = mp[k][b], mp[k][a]
            out.append((("L", k, a, b), G))
    return out


def all_moves(F, use_lam=True):
    mv = kempe_moves(F) + repairings(F)
    if use_lam:
        mv += lambda_repairings(F)
    return mv


def escape_bfs(F0, use_lam=True, maxdepth=8, cap=50000):
    """Least d such that some sequence of d moves, none raising Phi, ends below Phi(F0).
    Returns (d or None, [|L1|, |L2|, ...], status). L_d = new Phi-neutral frames after d moves."""
    p0 = phi(F0)
    seen = {key(F0)}
    level = [F0]
    sizes = []
    for d in range(1, maxdepth + 1):
        nxt = []
        for F in level:
            for name, G in all_moves(F, use_lam):
                pg = phi(G)
                if pg < p0:
                    return d, sizes, "escape"
                if pg == p0:
                    kg = key(G)
                    if kg not in seen:
                        seen.add(kg)
                        nxt.append(G)
        sizes.append(len(nxt))
        if not nxt:
            return None, sizes, "closed"
        if len(seen) > cap:
            return None, sizes, "cap"
        level = nxt
    return None, sizes, "maxdepth"


# ---------------------------------------------------------------- random hosts and frames

def random_host(M, rng, sweeps=60):
    """Random simple bipartite 6-regular graph by edge switches from the circulant
    i ~ M + (i + s mod M), s = 0..5 (a method different from the author's)."""
    E = [(i, M + (i + s) % M) for i in range(M) for s in range(6)]
    Es = set(E)
    for _ in range(sweeps * len(E)):
        a, b = rng.randrange(len(E)), rng.randrange(len(E))
        (u1, v1), (u2, v2) = E[a], E[b]
        if u1 == u2 or v1 == v2:
            continue
        if (u1, v2) in Es or (u2, v1) in Es:
            continue
        Es.discard((u1, v1)); Es.discard((u2, v2))
        E[a], E[b] = (u1, v2), (u2, v1)
        Es.add(E[a]); Es.add(E[b])
    return E


def maxflow_bmatch(m, edges, cap=4):
    """4-factor of a bipartite graph P, Q (0..m-1 each) with edge list (p, q): source->p cap 4,
    p->q cap 1, q->sink cap 4. Returns the chosen edge set or None."""
    S, T = 2 * m, 2 * m + 1
    adj = [[] for _ in range(2 * m + 2)]
    capd = {}

    def add(u, v, c):
        if (u, v) not in capd:
            adj[u].append(v); adj[v].append(u)
            capd[(u, v)] = 0; capd.setdefault((v, u), 0)
        capd[(u, v)] += c
    for p in range(m):
        add(S, p, cap)
    for q in range(m):
        add(m + q, T, cap)
    for p, q in edges:
        add(p, m + q, 1)
    total = 0
    while True:
        par = {S: None}
        dq = deque([S])
        while dq and T not in par:
            u = dq.popleft()
            for v in adj[u]:
                if v not in par and capd[(u, v)] > 0:
                    par[v] = u
                    dq.append(v)
        if T not in par:
            break
        v = T
        while par[v] is not None:
            u = par[v]
            capd[(u, v)] -= 1
            capd[(v, u)] += 1
            v = u
        total += 1
    if total < cap * m:
        return None
    return {(p, q) for p, q in edges if capd[(m + q, p)] > 0}


def perfect_matching(m, adjl):
    """Kuhn's algorithm; adjl[p] = list of q. Returns mate P->Q or None."""
    mq = [-1] * m

    def tryp(p, vis):
        for q in adjl[p]:
            if q in vis:
                continue
            vis.add(q)
            if mq[q] < 0 or tryp(mq[q], vis):
                mq[q] = p
                return True
        return False
    sys.setrecursionlimit(10000)
    for p in range(m):
        if not tryp(p, set()):
            return None
    mp = [0] * m
    for q, p in enumerate(mq):
        mp[p] = q
    return mp


def initial_frame(inst, rng):
    m = inst.m
    F4 = maxflow_bmatch(m, sorted(inst.Yedges))
    if F4 is None:
        return None
    rest = set(F4)
    mps = []
    for c in range(4):
        adjl = [[] for _ in range(m)]
        for p, q in rest:
            adjl[p].append(q)
        for a in adjl:
            rng.shuffle(a)
        pm = perfect_matching(m, adjl)
        assert pm is not None
        mps.append(pm)
        for p in range(m):
            rest.discard((p, pm[p]))
    assert not rest
    H = [(p, q, 0) for (p, q) in inst.Yedges if (p, q) not in F4]
    Qy = list(inst.Qy)
    rng.shuffle(Qy)
    H += [(p, q, 1) for p, q in zip(inst.Po, Qy)]
    incP = [[] for _ in range(m)]
    incQ = [[] for _ in range(m)]
    for idx, (p, q, l) in enumerate(H):
        incP[p].append(idx); incQ[q].append(idx)
    assert all(len(a) == 2 for a in incP) and all(len(a) == 2 for a in incQ)
    col = [None] * len(H)
    for start in range(m):
        if col[incP[start][0]] is not None:
            continue
        e = incP[start][0]
        c = 4
        p = start
        while col[e] is None:
            col[e] = c
            q = H[e][1]
            e2 = incQ[q][0] if incQ[q][0] != e else incQ[q][1]
            col[e2] = 9 - c
            p = H[e2][0]
            e = incP[p][0] if incP[p][0] != e2 else incP[p][1]
    mp4 = [None] * m; mp5 = [None] * m
    l4 = [0] * m; l5 = [0] * m
    for idx, (p, q, l) in enumerate(H):
        if col[idx] == 4:
            mp4[p] = q; l4[p] = l
        else:
            mp5[p] = q; l5[p] = l
    F = (mps + [mp4, mp5], [[0] * m for _ in range(4)] + [l4, l5])
    err = check_frame(inst, F)
    assert err is None, err
    return F


def random_walk(F, rng, steps=300):
    m = len(F[0][0])
    for _ in range(steps):
        if rng.random() < 0.8:
            i, k = rng.choice(PAIRS)
            x = rng.randrange(m)
            Z = next(Z for Z in kempe_components(F, i, k) if x in Z)
            if legal(F, i, k, Z):
                F = swap(F, i, k, Z)
        else:
            mv = lambda_repairings(F)
            if mv:
                F = rng.choice(mv)[1]
    perm = [0, 1, 2, 3]
    rng.shuffle(perm)
    F = ([F[0][c] for c in perm] + [F[0][4], F[0][5]], [F[1][c] for c in perm] + [F[1][4], F[1][5]])
    return F


def descend(F, rng):
    """random Phi-lowering single moves (Kempe swaps, re-pairings) until none exists"""
    while True:
        p = phi(F)
        if p == 2:
            return F
        low = [G for name, G in kempe_moves(F) + repairings(F) if phi(G) < p]
        if not low:
            return F
        F = rng.choice(low)
