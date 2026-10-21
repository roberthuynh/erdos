/* Independent brute-force checks for R20 (independent of ptool.c / brute_sparse.py).
   1. min of g(S) = 6|S| - 2e(S) over all S with 2 <= |S| <= n-1 (all 2^n subsets).
   2. every 4-factor F of G (enumerated by choosing the complement H with degree deg-4 at
      each vertex): is F connected, and does F have a cut of size <= 2 (test all pairs of edges).
   Input: edge list "n m" then m lines "u v". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int n, m, eu[200], ev[200], deg[32], need[32];
static uint32_t adj[32];
static long nfactors = 0, nconn = 0, ncut2 = 0, nbad = 0;
static int inH[200], hdeg[32];
static int connected_without(int skip1, int skip2) {
    /* F = edges not in H, minus edges skip1, skip2; BFS by bitmask */
    uint32_t fadj[32] = {0};
    for (int i = 0; i < m; i++) if (!inH[i] && i != skip1 && i != skip2) {
        fadj[eu[i]] |= 1u << ev[i]; fadj[ev[i]] |= 1u << eu[i]; }
    uint32_t seen = 1, frontier = 1;
    while (frontier) {
        uint32_t nf = 0;
        for (int v = 0; v < n; v++) if (frontier >> v & 1) nf |= fadj[v];
        nf &= ~seen; seen |= nf; frontier = nf;
    }
    return seen == ((n == 32) ? 0xffffffffu : ((1u << n) - 1));
}
static void check_factor(void) {
    nfactors++;
    int fe[200], k = 0;
    for (int i = 0; i < m; i++) if (!inH[i]) fe[k++] = i;
    if (!connected_without(-1, -1)) { return; }
    nconn++;
    int found = 0;
    for (int a = 0; a < k && !found; a++)
        for (int b = a + 1; b < k && !found; b++)
            if (!connected_without(fe[a], fe[b])) found = 1;
    if (found) ncut2++; else nbad++;
}
static void rec(int i) {
    /* choose H-edges in edge order; prune when some vertex can no longer reach its need */
    if (i == m) {
        for (int v = 0; v < n; v++) if (hdeg[v] != need[v]) return;
        check_factor(); return;
    }
    int u = eu[i], v = ev[i];
    /* option 1: edge i in H */
    if (hdeg[u] < need[u] && hdeg[v] < need[v]) {
        inH[i] = 1; hdeg[u]++; hdeg[v]++;
        rec(i + 1);
        inH[i] = 0; hdeg[u]--; hdeg[v]--;
    }
    /* option 2: edge i not in H; check u, v can still be completed */
    int remu = 0, remv = 0;
    for (int j = i + 1; j < m; j++) { if (eu[j] == u || ev[j] == u) remu++; if (eu[j] == v || ev[j] == v) remv++; }
    if (hdeg[u] + remu >= need[u] && hdeg[v] + remv >= need[v]) rec(i + 1);
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &n, &m) != 2) return 1;
    for (int i = 0; i < m; i++) { if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) return 1;
        adj[eu[i]] |= 1u << ev[i]; adj[ev[i]] |= 1u << eu[i]; deg[eu[i]]++; deg[ev[i]]++; }
    fclose(f);
    /* 1. brute-force sparsity */
    uint32_t N = 1u << n;
    uint8_t *e = malloc(N);
    e[0] = 0;
    int ming = 1 << 30; long cnt_min = 0; long cnt10 = 0;
    for (uint32_t S = 1; S < N; S++) {
        int low = __builtin_ctz(S);
        uint32_t R = S & (S - 1);
        e[S] = e[R] + __builtin_popcount(adj[low] & R);
        int s = __builtin_popcount(S);
        if (s >= 2 && s <= n - 1) {
            int g = 6 * s - 2 * e[S];
            if (g < ming) { ming = g; cnt_min = 0; }
            if (g == ming) cnt_min++;
            if (g == 10) cnt10++;
        }
    }
    printf("brute force: min g over 2<=|S|<=%d is %d (attained by %ld sets); g(V)=%d; #sets with g=10: %ld\n",
           n - 1, ming, cnt_min, 6 * n - 2 * e[N - 1], cnt10);
    free(e);
    /* 2. all 4-factors */
    for (int v = 0; v < n; v++) need[v] = deg[v] - 4;
    rec(0);
    printf("4-factors: %ld total, %ld connected; connected with a cut of size <= 2: %ld; connected without: %ld\n",
           nfactors, nconn, ncut2, nbad);
    return 0;
}
