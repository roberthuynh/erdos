/* mpair.c -- marked pair test (census/pairs-lane).
 * Input lines: "<graph6> a b c d" (ab, cd disjoint edges of the graph).
 * Decides whether there is a pair (C1, C2): two edge-disjoint cycles with the same vertex set S,
 * with edge ab on C1 and edge cd on C2 (a "compatible pair" for the marks ab, cd).
 * Exhaustive: every S containing a,b,c,d with min degree >= 4 in G[S]; every Hamilton cycle C1 of
 * G[S] through the edge ab and avoiding cd; then a Hamilton cycle of G[S] - E(C1) through cd.
 * Output: "<line> COMPAT" or "<line> NONE". Summary on stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint32_t mask;
static int n;
static mask adj[32], A1[32], res[32], S;
static int ssize, ea, eb, ec, ed, fx = -1, fy = -1;
static int path1[32];
static inline int pc(mask x) { return __builtin_popcount(x); }

static int ham2(int cur, mask visited, int depth) {
    if (depth == ssize) return (res[cur] >> ec) & 1;
    mask un = S & ~visited, ok = un | (1u << cur) | (1u << ec);
    for (mask t = un; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(res[v] & ok) < 2) return 0; }
    for (mask cand = res[cur] & un; cand; cand &= cand - 1) {
        int v = __builtin_ctz(cand);
        if (ham2(v, visited | (1u << v), depth + 1)) return 1;
    }
    return 0;
}
/* C1: path starting a -> b -> ... back to a, never using edge cd */
static int ham1(int cur, mask visited, int depth) {
    path1[depth - 1] = cur;
    if (depth == ssize) {
        if (!((A1[cur] >> ea) & 1)) return 0;
        for (mask t = S; t; t &= t - 1) { int v = __builtin_ctz(t); res[v] = adj[v] & S; }
        for (int i = 0; i < ssize; i++) { int x = path1[i], y = path1[(i + 1) % ssize]; res[x] &= ~(1u << y); res[y] &= ~(1u << x); }
        if (!((res[ec] >> ed) & 1)) return 0;
        /* C2 starts c -> d */
        return ham2(ed, (1u << ec) | (1u << ed), 2);
    }
    mask un = S & ~visited, ok = un | (1u << cur) | (1u << ea);
    for (mask t = un; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(A1[v] & ok) < 2) return 0; }
    for (mask cand = A1[cur] & un; cand; cand &= cand - 1) {
        int v = __builtin_ctz(cand);
        if (ham1(v, visited | (1u << v), depth + 1)) return 1;
    }
    return 0;
}
static int compat(void) {
    mask must = (1u << ea) | (1u << eb) | (1u << ec) | (1u << ed);
    mask full = (1u << n) - 1;
    mask core = full;
    for (int ch = 1; ch;) { ch = 0; for (mask t = core; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(adj[v] & core) < 4) { core &= ~(1u << v); ch = 1; } } }
    if ((core & must) != must) return 0;
    mask free = core & ~must;
    int idx[32], k = 0;
    for (mask t = free; t; t &= t - 1) idx[k++] = __builtin_ctz(t);
    for (long sub = 0; sub < (1L << k); sub++) {
        mask T = must;
        for (int i = 0; i < k; i++) if ((sub >> i) & 1) T |= 1u << idx[i];
        int good = 1;
        for (mask t = T; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(adj[v] & T) < 4) { good = 0; break; } }
        if (!good) continue;
        S = T; ssize = pc(T);
        for (mask t = T; t; t &= t - 1) { int v = __builtin_ctz(t); A1[v] = adj[v] & T; }
        A1[ec] &= ~(1u << ed); A1[ed] &= ~(1u << ec);
        if (fx >= 0) { A1[fx] &= ~(1u << fy); A1[fy] &= ~(1u << fx); }
        if (!((A1[ea] >> eb) & 1)) continue;
        path1[0] = ea; /* CORRECTION: the frozen mpair.c never sets path1[0] */
        if (ham1(eb, (1u << ea) | (1u << eb), 2)) return 1;
    }
    return 0;
}
int main(void) {
    static char line[4096];
    long tot = 0, hit = 0;
    while (fgets(line, sizeof line, stdin)) {
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        if (!L) continue;
        char g6[256]; fx = fy = -1;
        int got = sscanf(line, "%255s %d %d %d %d %d %d", g6, &ea, &eb, &ec, &ed, &fx, &fy);
        if (got != 5 && got != 7) { fprintf(stderr, "bad line\n"); return 2; }
        if (got == 5) fx = fy = -1;
        n = g6[0] - 63;
        memset(adj, 0, sizeof adj);
        int bit = 0, pos = 1;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int ch = g6[pos] - 63;
            if ((ch >> (5 - bit)) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            if (++bit == 6) { bit = 0; pos++; }
        }
        if (!((adj[ea] >> eb) & 1) || !((adj[ec] >> ed) & 1)) { fprintf(stderr, "marks not edges: %s\n", line); return 2; }
        tot++;
        int r = compat();
        hit += r;
        printf("%s %s\n", line, r ? "COMPAT" : "NONE");
    }
    fprintf(stderr, "lines=%ld compat=%ld none=%ld\n", tot, hit, tot - hit);
    return 0;
}
