#!/usr/bin/env python3
"""Check a frame certificate (JSON with M, B_edges, o, y, Yplus_edges = [u, v, virtual, colour]).
Usage: cert.py FILE [brute|flow|skip] [maxdepth]
Prints: host checks, minimum essential cut, frame validity, Phi, single-move table, BFS escape
depth with and without Lambda re-pairings."""
import sys, json, time
from collections import Counter
sys.path.insert(0, __import__("os").path.dirname(__file__))
from s6rev import *


def load(path):
    d = json.load(open(path))
    M = d["M"]
    inst = Inst(M, [tuple(e) for e in d["B_edges"]], d["o"], d["y"])
    m = inst.m
    mp = [[None] * m for _ in range(6)]
    lam = [[0] * m for _ in range(6)]
    for u, v, virt, c in d["Yplus_edges"]:
        i, o_ = (u, v) if u < M else (v, u)
        p, q = inst.pidx[o_], inst.qidx[i]
        if mp[c][p] is not None:
            raise ValueError("vertex %d has two edges of colour %d" % (o_, c))
        mp[c][p] = q
        lam[c][p] = 1 if virt else 0
    if any(x is None for row in mp for x in row):
        raise ValueError("some colour class misses a vertex")
    return d, inst, (mp, lam)


def girth(adj):
    n = len(adj)
    g = None
    for s in range(n):
        dist = {s: 0}
        par = {s: None}
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    par[v] = u
                    dq.append(v)
                elif par[u] != v:
                    c = dist[u] + dist[v] + 1
                    if g is None or c < g:
                        g = c
    return g


def main():
    path = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 else "flow"
    maxdepth = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    d, inst, F = load(path)
    M = inst.M
    print("file", path, "M", M, "|B|", 2 * M, "o", inst.o, "y", inst.y)
    print("B: simple, bipartite (I = 0..M-1), 6-regular: OK; girth", girth(inst.adj))
    t = time.time()
    if mode == "brute":
        print("min essential cut (brute force over all 2^(n-1) sets):", min_ess_cut_brute(inst.adj),
              "%.1fs" % (time.time() - t))
    elif mode == "flow":
        print("min(10, min essential cut) by flows over all disjoint edge pairs:",
              min_ess_cut_flow(inst.adj, 10), "%.1fs" % (time.time() - t))
    err = check_frame(inst, F)
    print("frame check:", "OK" if err is None else err)
    mp, lam = F
    cC, cC2 = ncyc(mp[0], mp[1]), ncyc(mp[2], mp[3])
    print("c(C) =", cC, " c(C') =", cC2, " Phi =", cC + cC2, " (file says Phi = %s)" % d.get("Phi"))
    L = sorted((inst.Pl[p], inst.Ql[mp[c][p]], c) for c in (4, 5) for p in range(inst.m) if lam[c][p])
    print("Lambda edges (O-vertex, I-vertex, colour):", L)
    print("c(H + Lambda) =", ncyc(mp[4], mp[5]), " m =", inst.m)
    # single moves
    km = kempe_moves(F)
    tab = Counter()
    for name, G in km:
        tab[(name[1], name[2], phi(G))] += 1
    nontriv = [(name, G) for name, G in km if key(G) != key(F)]
    print("legal Kempe swaps: %d (of which change the frame: %d)" % (len(km), len(nontriv)))
    allK = sum(len(kempe_components(F, i, k)) for i, k in PAIRS)
    print("all Kempe chains (legal or not): %d" % allK)
    by_pair = Counter()
    for (i, k, ph), c in sorted(tab.items()):
        by_pair[(i, k)] += c
    print("legal swaps per colour pair:", dict(sorted(by_pair.items())))
    print("Phi after legal swaps:", dict(Counter(phi(G) for _, G in km)))
    print("Phi after legal swaps that touch C or C' (pairs other than (0,1),(2,3),(4,5)):",
          dict(Counter(phi(G) for name, G in km if (name[1], name[2]) not in ((0, 1), (2, 3), (4, 5)))))
    print("Phi after the two re-pairings:", [phi(G) for _, G in repairings(F)])
    print("Lambda re-pairings available:", len(lambda_repairings(F)))
    for use_lam in (True, False):
        t = time.time()
        r = escape_bfs(F, use_lam=use_lam, maxdepth=maxdepth, cap=400000)
        print("BFS escape (Lambda re-pairings %s): depth %s, new Phi-neutral frames per level %s, %s, %.1fs"
              % ("ON" if use_lam else "OFF", r[0], r[1], r[2], time.time() - t))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
