#!/usr/bin/env python3
"""Check a pair certificate against a host graph, in pure Python.

A certificate is two vertex sequences. Each must be a simple cycle of length >= 3 in the host
(consecutive vertices adjacent, including last to first, no repeated vertex). The two cycles must
have exactly the same vertex set and share no edge.
"""
import json, sys


def check(edges, cyc1, cyc2):
    E = set()
    for a, b in edges:
        a, b = int(a), int(b)
        if a == b:
            return False, "host has a loop"
        E.add(frozenset((a, b)))

    def cycle_edges(c):
        c = [int(v) for v in c]
        if len(c) < 3:
            raise ValueError("cycle shorter than 3")
        if len(set(c)) != len(c):
            raise ValueError("repeated vertex")
        es = set()
        for i in range(len(c)):
            e = frozenset((c[i], c[(i + 1) % len(c)]))
            if e not in E:
                raise ValueError("non-edge %s" % sorted(e))
            es.add(e)
        if len(es) != len(c):
            raise ValueError("edge repeated")
        return es

    try:
        e1, e2 = cycle_edges(cyc1), cycle_edges(cyc2)
    except ValueError as err:
        return False, str(err)
    if set(map(int, cyc1)) != set(map(int, cyc2)):
        return False, "vertex sets differ"
    if e1 & e2:
        return False, "shared edge"
    return True, "valid pair on %d vertices" % len(cyc1)


if __name__ == "__main__":
    g = json.load(open(sys.argv[1]))
    cert = json.load(open(sys.argv[2]))
    ok, msg = check(g["edges"], cert["cycles"][0], cert["cycles"][1])
    print(("OK " if ok else "FAIL ") + msg)
    sys.exit(0 if ok else 1)
