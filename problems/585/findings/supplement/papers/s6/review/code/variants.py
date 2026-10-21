#!/usr/bin/env python3
"""Level sizes of the Phi-neutral BFS under several frame-identification conventions."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from s6rev import *
from cert import load

def mk(F):
    mp, lam = F
    m = len(mp[0])
    return [bytes(mp[c][p] + (m if lam[c][p] else 0) for p in range(m)) for c in range(6)]

KEYS = {
  "labelled": lambda F: tuple(mk(F)),
  "45unordered": lambda F: (tuple(mk(F)[:4]), tuple(sorted(mk(F)[4:]))),
  "pairs-unordered-within": lambda F: (tuple(sorted(mk(F)[0:2])), tuple(sorted(mk(F)[2:4])), tuple(sorted(mk(F)[4:]))),
  "quotient(G)": key,
  "C,C' edge sets + leftover": lambda F: (tuple(sorted((tuple(sorted(set(zip(range(len(F[0][0])), F[0][0])) | set(zip(range(len(F[0][0])), F[0][1])))),
                                                        tuple(sorted(set(zip(range(len(F[0][0])), F[0][2])) | set(zip(range(len(F[0][0])), F[0][3]))))))),
                                          tuple(sorted(mk(F)[4:]))),
}

def bfs(F0, keyf, use_lam, maxdepth=4):
    p0 = phi(F0); seen = {keyf(F0)}; level = [F0]; sizes = []
    for d in range(1, maxdepth + 1):
        nxt = []; low = 0
        for F in level:
            for name, G in all_moves(F, use_lam):
                pg = phi(G)
                if pg < p0:
                    low += 1
                elif pg == p0:
                    kg = keyf(G)
                    if kg not in seen:
                        seen.add(kg); nxt.append(G)
        sizes.append((len(nxt), "lowering moves from level %d: %d" % (d - 1, low)))
        if low:
            return d, sizes
        level = nxt
    return None, sizes

d, inst, F = load(sys.argv[1])
for name, kf in KEYS.items():
    for ul in (True, False):
        r = bfs(F, kf, ul)
        print("%-28s Lambda %-3s escape depth %s  levels %s" % (name, "ON" if ul else "OFF", r[0], [s[0] for s in r[1]]), [s[1] for s in r[1]][-1])
