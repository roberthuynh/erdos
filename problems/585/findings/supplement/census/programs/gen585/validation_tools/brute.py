#!/usr/bin/env python3
"""Exhaustive pair decider for small graphs. No SAT, no networkx.

For every vertex set S with |S| >= 5 and minimum degree >= 4 in G[S] (a necessary condition),
enumerate every Hamilton cycle of G[S] as an edge bitmask and test pairwise edge-disjointness.
Exact, exponential; intended for n <= 14 or sparse graphs.
"""
import json, sys
from itertools import combinations


def decide(n, edges, max_cycles_per_support=None):
    eid = {}
    adj = [0] * n
    for a, b in edges:
        a, b = int(a), int(b)
        key = (min(a, b), max(a, b))
        if key not in eid:
            eid[key] = len(eid)
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    # 4-core, by peeling
    alive = (1 << n) - 1
    changed = True
    while changed:
        changed = False
        for v in range(n):
            if alive >> v & 1 and bin(adj[v] & alive).count("1") < 4:
                alive &= ~(1 << v)
                changed = True
    core = [v for v in range(n) if alive >> v & 1]
    for size in range(5, len(core) + 1):
        for S in combinations(core, size):
            mask = 0
            for v in S:
                mask |= 1 << v
            if any(bin(adj[v] & mask).count("1") < 4 for v in S):
                continue
            res = _pair_in_support(S, mask, adj, eid, max_cycles_per_support)
            if res is not None:
                return {"status": "PAIR", "support": list(S), "cycles": res}
    return {"status": "NOPAIR"}


def _pair_in_support(S, mask, adj, eid, cap):
    v0 = S[0]
    k = len(S)
    found = []  # (edge mask, order)

    def emask(order):
        m = 0
        for i in range(k):
            a, b = order[i], order[(i + 1) % k]
            m |= 1 << eid[(min(a, b), max(a, b))]
        return m

    path = [v0]
    used = 1 << v0
    result = []

    def dfs(cur):
        nonlocal used
        if len(path) == k:
            if adj[cur] >> v0 & 1 and path[1] < path[-1]:
                m = emask(path)
                for m2, o2 in found:
                    if m & m2 == 0:
                        result.append((list(path), o2))
                        return True
                found.append((m, list(path)))
                if cap is not None and len(found) > cap:
                    raise RuntimeError("cycle cap exceeded")
            return False
        nb = adj[cur] & mask & ~used
        while nb:
            low = nb & -nb
            w = low.bit_length() - 1
            nb ^= low
            path.append(w)
            used |= low
            if dfs(w):
                return True
            path.pop()
            used ^= low
        return False

    if dfs(v0):
        return result[0]
    return None


if __name__ == "__main__":
    d = json.load(open(sys.argv[1]))
    edges = d["edges"]
    n = d.get("n", 1 + max(max(e) for e in edges))
    print(json.dumps(decide(n, edges)))
