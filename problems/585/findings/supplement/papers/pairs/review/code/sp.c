/* sp.c: independent test for two edge-disjoint Hamilton cycles (any max degree).
   Enumerate Hamilton cycles C through vertex 0 (one direction); for each, search a Hamilton cycle in
   G - E(C). Output: g6 SP/NOSP number_of_first_cycles_tried. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n; static uint32_t adj[32], rem[32];
static int path[32], path2[32]; static long tried; static int found;
static int ham2(int u, int len, uint32_t vis) {
    if (len == n) return (rem[u] & 1) != 0;
    uint32_t nb = rem[u] & ~vis;
    while (nb) { int w = __builtin_ctz(nb); nb &= nb - 1;
        if (ham2(w, len + 1, vis | 1u << w)) return 1; }
    return 0;
}
static void dfs(int u, int len, uint32_t vis) {
    if (found) return;
    if (len == n) {
        if (!(adj[u] & 1)) return;
        tried++;
        memcpy(rem, adj, sizeof(uint32_t) * n);
        for (int i = 0; i < n; i++) { int x = path[i], y = path[(i + 1) % n]; rem[x] &= ~(1u << y); rem[y] &= ~(1u << x); }
        for (int v = 0; v < n; v++) if (__builtin_popcount(rem[v]) < 2) return;
        if (ham2(0, 1, 1u)) found = 1;
        return;
    }
    uint32_t nb = adj[u] & ~vis;
    while (nb) { int w = __builtin_ctz(nb); nb &= nb - 1;
        if (len == n - 1 && w < path[1]) continue;
        path[len] = w; dfs(w, len + 1, vis | 1u << w); if (found) return; }
}
int main(void) {
    char line[1024];
    while (fgets(line, sizeof line, stdin)) {
        char g6[512]; if (sscanf(line, "%511s", g6) != 1 || g6[0] == '>') continue;
        n = g6[0] - 63; memset(adj, 0, sizeof adj); int k = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int byte = g6[1 + k / 6] - 63; int bit = (byte >> (5 - k % 6)) & 1; k++;
            if (bit) { adj[i] |= 1u << j; adj[j] |= 1u << i; } }
        tried = 0; found = 0; path[0] = 0; dfs(0, 1, 1u);
        printf("%s %s %ld\n", g6, found ? "SP" : "NOSP", tried); fflush(stdout);
    }
    return 0;
}
