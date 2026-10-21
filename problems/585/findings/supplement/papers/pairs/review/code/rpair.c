/* rpair.c: an independent pair tester, written without reading pairc/mpair/ptool.
   A pair = two edge-disjoint cycles with the same vertex set.
   Method: list every cycle once (DFS from its smallest vertex, one direction), store
   (vertex mask, edge mask), sort by vertex mask, and look for two edge-disjoint cycles in a group.
   Input: one graph per line, graph6 (n <= 31, <= 64 edges), then optional integers.
   Modes (argv[1]):
     f        : "PAIR"/"FREE" per graph.
     t        : line = g6 a b c d. ab, cd must be edges. Reports: Y has a pair with ab on one cycle and
                cd on the other (YES/NO); Y - ab - cd pair-free (FREE/PAIR); Y has some pair (PAIR/FREE).
     r        : line = g6 v. v has degree 4. Reports the set of pairings of N(v) realised by pairs
                through v (as 3 bits: {n0n1|n2n3}, {n0n2|n1n3}, {n0n3|n1n2}) and whether some pair avoids v. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef struct { uint32_t vm; uint64_t em; } cyc_t;
static int n, m, eid[32][32];
static uint32_t adj[32];
static cyc_t *cy; static long ncy, capcy;
static int path[32], plen;
static uint64_t pem;
static void add_cycle(uint32_t vm, uint64_t em) {
    if (ncy == capcy) { capcy = capcy ? 2 * capcy : 1 << 16; cy = realloc(cy, capcy * sizeof(cyc_t)); }
    cy[ncy].vm = vm; cy[ncy].em = em; ncy++;
}
static void dfs(int s, int u, uint32_t vm) {
    /* path[0] = s, ..., path[plen-1] = u */
    if (plen >= 3 && (adj[u] >> s & 1) && path[1] < u)
        add_cycle(vm, pem | (1ULL << eid[u][s]));
    uint32_t nb = adj[u] & ~vm & ~((2u << s) - 1);  /* vertices > s not on the path */
    while (nb) {
        int w = __builtin_ctz(nb); nb &= nb - 1;
        path[plen++] = w; uint64_t old = pem; pem |= 1ULL << eid[u][w];
        dfs(s, w, vm | (1u << w));
        pem = old; plen--;
    }
}
static int cmpc(const void *a, const void *b) {
    const cyc_t *x = a, *y = b;
    if (x->vm != y->vm) return x->vm < y->vm ? -1 : 1;
    return 0;
}
static int parse_g6(const char *s) {
    n = s[0] - 63; if (n < 1 || n > 31) return -1;
    memset(adj, 0, sizeof adj); m = 0;
    int k = 0; const char *p = s + 1;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        int byte = p[k / 6] - 63; int bit = (byte >> (5 - k % 6)) & 1; k++;
        if (bit) { adj[i] |= 1u << j; adj[j] |= 1u << i; eid[i][j] = eid[j][i] = m++; }
    }
    return m <= 64 ? 0 : -1;
}
static void all_cycles(void) {
    ncy = 0;
    for (int s = 0; s < n; s++) { path[0] = s; plen = 1; pem = 0; dfs(s, s, 1u << s); }
    qsort(cy, ncy, sizeof(cyc_t), cmpc);
}
/* any edge-disjoint pair among cycles; optional mask restrictions:
   need1: edges cycle 1 must contain; need2: edges cycle 2 must contain; avoidv: vertex mask both must avoid (0 = none),
   needv: vertex mask both must contain */
static int find_pair(uint64_t need1, uint64_t need2, uint32_t avoidv, uint32_t needv) {
    long i = 0;
    while (i < ncy) {
        long j = i; while (j < ncy && cy[j].vm == cy[i].vm) j++;
        uint32_t vm = cy[i].vm;
        if (!(vm & avoidv) && (vm & needv) == needv && j - i >= 2) {
            for (long a = i; a < j; a++) {
                if ((cy[a].em & need1) != need1) continue;
                for (long b = i; b < j; b++) {
                    if (b == a) continue;
                    if ((cy[b].em & need2) != need2) continue;
                    if ((cy[a].em & cy[b].em) == 0) return 1;
                }
            }
        }
        i = j;
    }
    return 0;
}
int main(int argc, char **argv) {
    char mode = argv[1][0];
    char line[4096];
    long lines = 0;
    while (fgets(line, sizeof line, stdin)) {
        char g6[512]; int off = 0;
        if (sscanf(line, "%511s%n", g6, &off) != 1) continue;
        if (parse_g6(g6) < 0) { printf("BADGRAPH\n"); continue; }
        lines++;
        if (mode == 'f') {
            all_cycles();
            printf("%s %s %ld\n", g6, find_pair(0, 0, 0, 0) ? "PAIR" : "FREE", ncy);
        } else if (mode == 't') {
            int a, b, c, d;
            if (sscanf(line + off, "%d %d %d %d", &a, &b, &c, &d) != 4) { printf("BADMARKS\n"); continue; }
            if (!(adj[a] >> b & 1) || !(adj[c] >> d & 1) || a == c || a == d || b == c || b == d) { printf("MARKS-NOT-DISJOINT-EDGES\n"); continue; }
            uint64_t eab = 1ULL << eid[a][b], ecd = 1ULL << eid[c][d];
            all_cycles();
            int compat = find_pair(eab, ecd, 0, 0);
            int anyp = find_pair(0, 0, 0, 0);
            long ny = ncy;
            /* Z = Y - ab - cd: rebuild adjacency without the two edges and re-enumerate */
            adj[a] &= ~(1u << b); adj[b] &= ~(1u << a); adj[c] &= ~(1u << d); adj[d] &= ~(1u << c);
            all_cycles();
            int zp = find_pair(0, 0, 0, 0);
            int nn = n, ee = 0, maxd = 0;
            adj[a] |= 1u << b; adj[b] |= 1u << a; adj[c] |= 1u << d; adj[d] |= 1u << c;
            for (int v = 0; v < nn; v++) { int dg = __builtin_popcount(adj[v]); ee += dg; if (dg > maxd) maxd = dg; }
            printf("%s %d %d %d %d n=%d e=%d maxdeg=%d cyclesY=%ld compatible=%s Ypair=%s Z=%s\n", g6, a, b, c, d,
                   nn, ee / 2, maxd, ny, compat ? "YES" : "NO", anyp ? "PAIR" : "FREE", zp ? "PAIR" : "FREE");
        } else if (mode == 'r') {
            int v; if (sscanf(line + off, "%d", &v) != 1) { printf("BADV\n"); continue; }
            int nb[4], k = 0;
            for (int w = 0; w < n; w++) if (adj[v] >> w & 1) { if (k < 4) nb[k] = w; k++; }
            if (k != 4) { printf("%s DEG%d\n", g6, k); continue; }
            all_cycles();
            int pr[3][4] = {{0,1,2,3},{0,2,1,3},{0,3,1,2}}; int real = 0;
            for (int t = 0; t < 3; t++) {
                uint64_t n1 = (1ULL << eid[v][nb[pr[t][0]]]) | (1ULL << eid[v][nb[pr[t][1]]]);
                uint64_t n2 = (1ULL << eid[v][nb[pr[t][2]]]) | (1ULL << eid[v][nb[pr[t][3]]]);
                if (find_pair(n1, n2, 0, 1u << v)) real |= 1 << t;
            }
            int avoid = find_pair(0, 0, 1u << v, 0);
            printf("%s %d realised=%d%d%d count=%d pair_avoiding_v=%s cycles=%ld\n", g6, v, real & 1, real >> 1 & 1, real >> 2 & 1,
                   __builtin_popcount(real), avoid ? "YES" : "NO", ncy);
        }
        fflush(stdout);
    }
    return 0;
}
