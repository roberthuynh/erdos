/* hd.c: independent Hamilton-decomposition test for 4-regular graphs (written without reading ptool.c).
   For each graph6 line: checks 4-regularity and connectivity, finds whether some set of <= 2 edges
   disconnects it (all pairs of edges), and searches for a Hamilton cycle C (DFS from vertex 0) such that
   G - E(C) is connected (then it is one Hamilton cycle, being 2-regular and spanning).
   Output: g6 REG4|NOTREG conn=0/1 cut2=0/1 HD/NOTHD hamcycles_tried */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n, m, eu[128], ev[128], eid[32][32];
static uint32_t adj[32];
static int path[32]; static long tried; static int found;
static uint32_t cadj[32];
static int connected_mask(uint32_t *a) {
    uint32_t seen = 1, fr = 1, all = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    while (fr) { uint32_t nf = 0; for (int v = 0; v < n; v++) if (fr >> v & 1) nf |= a[v]; nf &= ~seen; seen |= nf; fr = nf; }
    return seen == all;
}
static void dfs(int u, int len, uint32_t vis) {
    if (found) return;
    if (len == n) {
        if (!(adj[u] & 1)) return;
        /* cycle path[0..n-1] + edge u-0; complement adjacency */
        tried++;
        uint32_t a[32]; memcpy(a, adj, sizeof(uint32_t) * n);
        for (int i = 0; i < n; i++) { int x = path[i], y = path[(i + 1) % n]; a[x] &= ~(1u << y); a[y] &= ~(1u << x); }
        if (connected_mask(a)) found = 1;
        return;
    }
    uint32_t nb = adj[u] & ~vis;
    while (nb) { int w = __builtin_ctz(nb); nb &= nb - 1;
        if (len == n - 1 && w < path[1]) continue; /* one direction per cycle */
        path[len] = w; dfs(w, len + 1, vis | 1u << w); if (found) return; }
}
int main(void) {
    char line[1024];
    while (fgets(line, sizeof line, stdin)) {
        char g6[512]; if (sscanf(line, "%511s", g6) != 1) continue;
        n = g6[0] - 63; memset(adj, 0, sizeof adj); m = 0;
        int k = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int byte = g6[1 + k / 6] - 63; int bit = (byte >> (5 - k % 6)) & 1; k++;
            if (bit) { adj[i] |= 1u << j; adj[j] |= 1u << i; eu[m] = i; ev[m] = j; eid[i][j] = eid[j][i] = m; m++; } }
        int reg = 1; for (int v = 0; v < n; v++) if (__builtin_popcount(adj[v]) != 4) reg = 0;
        int conn = connected_mask(adj);
        int cut2 = !conn;
        for (int a = 0; a < m && !cut2; a++) for (int b = a; b < m && !cut2; b++) {
            memcpy(cadj, adj, sizeof(uint32_t) * n);
            cadj[eu[a]] &= ~(1u << ev[a]); cadj[ev[a]] &= ~(1u << eu[a]);
            cadj[eu[b]] &= ~(1u << ev[b]); cadj[ev[b]] &= ~(1u << eu[b]);
            if (!connected_mask(cadj)) cut2 = 1;
        }
        tried = 0; found = 0;
        if (reg && conn) { path[0] = 0; dfs(0, 1, 1u); }
        printf("%s %s conn=%d cut2=%d %s %ld\n", g6, reg ? "REG4" : "NOTREG", conn, cut2, found ? "HD" : "NOTHD", tried);
        fflush(stdout);
    }
    return 0;
}
