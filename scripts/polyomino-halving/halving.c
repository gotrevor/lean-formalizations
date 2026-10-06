/* Redelmeier enumeration of fixed polyominoes, with an exact-halving check.
 *
 * For every even size N = 2m it counts H(N): polyominoes with a bridge (an edge of the induced
 * grid graph whose removal disconnects it) splitting the cells m + m, and E(N): the total
 * number of such bridges.  Usage: halving NMAX [JOB NJOBS SPLITDEPTH].  Output lines:
 *   n A(n) H(n) E(n)          (H, E are 0 for odd n)
 * With NJOBS > 1, subtrees rooted at size SPLITDEPTH are dealt round-robin; job 0 alone
 * counts sizes <= SPLITDEPTH, so summing the jobs' outputs gives the totals.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NMAX 24
#define W (2 * NMAX + 3)
#define HGT (NMAX + 2)

static int N, job = 0, njobs = 1, split = 0;
static long long dealt = 0;
static unsigned long long A[NMAX + 1], Hc[NMAX + 1], Ec[NMAX + 1];
static unsigned char seen[HGT * W];
static int idx[HGT * W];          /* cell -> position in P, or -1 */
static int P[NMAX];
static const int dir[4] = {1, -1, W, -W};

/* bridges with subtree sizes, iterative-free small DFS (n <= 24) */
static int tin[NMAX], low[NMAX], sub[NMAX], timer_, nP, half, nbr;
static void dfs(int u, int parent) {
    tin[u] = low[u] = timer_++;
    sub[u] = 1;
    for (int d = 0; d < 4; d++) {
        int v = idx[P[u] + dir[d]];
        if (v < 0 || v == parent) continue;
        if (tin[v] >= 0) { if (tin[v] < low[u]) low[u] = tin[v]; }
        else {
            dfs(v, u);
            sub[u] += sub[v];
            if (low[v] < low[u]) low[u] = low[v];
            if (low[v] > tin[u] && sub[v] == half) nbr++;
        }
    }
}

static void record(int n) {
    if (njobs > 1 && n <= split && job != 0) return;
    A[n]++;
    if (n % 2) return;
    nP = n; half = n / 2; nbr = 0; timer_ = 0;
    for (int i = 0; i < n; i++) tin[i] = -1;
    dfs(0, -1);
    if (nbr) { Hc[n]++; Ec[n] += nbr; }
}

static void rec(int *untried, int nu, int size) {
    int newu[4 * NMAX + 4];
    for (int i = nu - 1; i >= 0; i--) {
        int c = untried[i];
        if (njobs > 1 && size + 1 == split) {
            if ((dealt++ % njobs) != job) continue;
        }
        P[size] = c; idx[c] = size;
        record(size + 1);
        if (size + 1 < N) {
            int k = 0;
            for (int j = 0; j < i; j++) newu[k++] = untried[j];
            int added[4], na = 0;
            for (int d = 0; d < 4; d++) {
                int e = c + dir[d];
                if (!seen[e]) { seen[e] = 1; newu[k++] = e; added[na++] = e; }
            }
            rec(newu, k, size + 1);
            for (int a = 0; a < na; a++) seen[added[a]] = 0;
        }
        idx[c] = -1;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: halving NMAX [JOB NJOBS SPLITDEPTH]\n"); return 2; }
    N = atoi(argv[1]);
    if (N < 1 || N > NMAX) { fprintf(stderr, "NMAX must be in 1..%d\n", NMAX); return 2; }
    if (argc >= 5) { job = atoi(argv[2]); njobs = atoi(argv[3]); split = atoi(argv[4]); }
    for (int i = 0; i < HGT * W; i++) idx[i] = -1;
    memset(seen, 0, sizeof seen);
    int ox = NMAX + 1;                      /* x offset: column of x = 0 */
    /* forbid y = 0, x < 0, and every border cell, so the origin is the (y, x)-lex least cell */
    for (int y = 0; y < HGT; y++)
        for (int x = 0; x < W; x++) {
            int c = y * W + x;
            if (y == 0 || y == HGT - 1 || x == 0 || x == W - 1) seen[c] = 1;
            if (y == 1 && x < ox) seen[c] = 1;
        }
    int origin = 1 * W + ox;
    seen[origin] = 1;
    int u[1] = {origin};
    rec(u, 1, 0);
    for (int n = 1; n <= N; n++) printf("%d %llu %llu %llu\n", n, A[n], Hc[n], Ec[n]);
    return 0;
}
