/* genbip.c: independent generator of bipartite graphs with colour classes of sizes R (rows) and
   C (columns), C <= 8, R <= 8, degrees in [dmin, dmax] on both sides, exactly E edges, up to
   colour-preserving isomorphism (row and column permutations; the two classes are never swapped).
   Method: rows chosen as a non-increasing multiset of bitmasks (one representative per row
   permutation), pruned on column sums and edge count; canonical form = lexicographic minimum over all
   column permutations of the sorted row list; duplicates removed by sorting the canonical forms.
   Output: graph6, vertices 0..R-1 = rows, R..R+C-1 = columns. Usage: genbip R C dmin dmax E */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int R, C, dmin, dmax, E;
static int opts[256], nopt;
static int rows[8], colsum[8];
static int perms[40320][8], nperm;
static uint64_t *canon; static long ncanon, capcanon;
static long leaves = 0;
static void mkperms(int k, int *p, int used) {
    if (k == C) { memcpy(perms[nperm++], p, sizeof(int) * C); return; }
    for (int i = 0; i < C; i++) if (!(used >> i & 1)) { p[k] = i; mkperms(k + 1, p, used | 1 << i); }
}
static int cmpu8(const void *a, const void *b) { return (int)*(const uint8_t *)a - (int)*(const uint8_t *)b; }
static uint64_t canonical(void) {
    uint64_t best = UINT64_MAX;
    for (int t = 0; t < nperm; t++) {
        uint8_t r[8];
        for (int i = 0; i < R; i++) {
            int x = 0;
            for (int j = 0; j < C; j++) if (rows[i] >> j & 1) x |= 1 << perms[t][j];
            r[i] = (uint8_t)x;
        }
        qsort(r, R, 1, cmpu8);
        uint64_t key = 0;
        for (int i = 0; i < R; i++) key = (key << 8) | r[i];
        if (key < best) best = key;
    }
    return best;
}
static void rec(int i, int startopt, int edges) {
    if (i == R) {
        if (edges != E) return;
        for (int j = 0; j < C; j++) if (colsum[j] < dmin || colsum[j] > dmax) return;
        leaves++;
        if (ncanon == capcanon) { capcanon = capcanon ? 2 * capcanon : 1024; canon = realloc(canon, capcanon * 8); }
        canon[ncanon++] = canonical();
        return;
    }
    int left = R - i;
    for (int o = startopt; o < nopt; o++) {
        int x = opts[o], d = __builtin_popcount(x);
        /* edge-count pruning: remaining rows have degree in [dmin, dmax] */
        int ne = edges + d;
        if (ne + (left - 1) * dmin > E || ne + (left - 1) * dmax < E) continue;
        int ok = 1;
        for (int j = 0; j < C; j++) {
            int s = colsum[j] + (x >> j & 1);
            if (s > dmax) { ok = 0; break; }
            if (s + (left - 1) < dmin) { ok = 0; break; }
        }
        if (!ok) continue;
        rows[i] = x; for (int j = 0; j < C; j++) colsum[j] += x >> j & 1;
        rec(i + 1, o, ne);
        for (int j = 0; j < C; j++) colsum[j] -= x >> j & 1;
    }
}
static int cmpu64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
static void print_g6(uint64_t key) {
    int n = R + C; int adj[16][16] = {{0}};
    for (int i = R - 1; i >= 0; i--) { int x = key & 0xff; key >>= 8;
        for (int j = 0; j < C; j++) if (x >> j & 1) adj[i][R + j] = adj[R + j][i] = 1; }
    char out[64]; int k = 0, byte = 0, nb = 0; out[k++] = (char)(n + 63);
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        byte = (byte << 1) | adj[i][j]; nb++;
        if (nb == 6) { out[k++] = (char)(byte + 63); byte = 0; nb = 0; } }
    if (nb) { byte <<= (6 - nb); out[k++] = (char)(byte + 63); }
    out[k] = 0; puts(out);
}
int main(int argc, char **argv) {
    R = atoi(argv[1]); C = atoi(argv[2]); dmin = atoi(argv[3]); dmax = atoi(argv[4]); E = atoi(argv[5]);
    /* options: masks over C columns with popcount in [dmin, dmax], in decreasing numeric order */
    for (int x = (1 << C) - 1; x >= 0; x--) { int d = __builtin_popcount(x); if (d >= dmin && d <= dmax) opts[nopt++] = x; }
    int p[8]; mkperms(0, p, 0);
    rec(0, 0, 0);
    qsort(canon, ncanon, 8, cmpu64);
    long u = 0;
    for (long i = 0; i < ncanon; i++) if (i == 0 || canon[i] != canon[i - 1]) canon[u++] = canon[i];
    fprintf(stderr, "R=%d C=%d deg[%d,%d] E=%d: %ld row-multisets, %ld classes\n", R, C, dmin, dmax, E, leaves, u);
    for (long i = 0; i < u; i++) print_g6(canon[i]);
    return 0;
}
