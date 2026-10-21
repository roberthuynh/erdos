/* sparse_bf.c: brute-force sparsity, graph6 lines on stdin (n <= 24): prints "g6 min_g" where min_g is
   the minimum of 6|S| - 2e(S) over 2 <= |S| <= n-1 (all subsets). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(void) {
    char line[1024]; uint8_t *e = malloc(1u << 24);
    while (fgets(line, sizeof line, stdin)) {
        char g6[512]; if (sscanf(line, "%511s", g6) != 1) continue;
        int n = g6[0] - 63; uint32_t adj[32] = {0}; int k = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int byte = g6[1 + k / 6] - 63; int bit = (byte >> (5 - k % 6)) & 1; k++;
            if (bit) { adj[i] |= 1u << j; adj[j] |= 1u << i; } }
        uint32_t N = 1u << n; int ming = 1 << 30; e[0] = 0;
        for (uint32_t S = 1; S < N; S++) {
            int low = __builtin_ctz(S); uint32_t R = S & (S - 1);
            e[S] = e[R] + __builtin_popcount(adj[low] & R);
            int s = __builtin_popcount(S);
            if (s >= 2 && s <= n - 1) { int g = 6 * s - 2 * e[S]; if (g < ming) ming = g; }
        }
        printf("%s %d\n", g6, ming); fflush(stdout);
    }
    return 0;
}
