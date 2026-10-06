/* Redelmeier enumeration of fixed polyominoes, with an exact-halving check.
 *
 * For every even size N = 2m it counts H(N): polyominoes with a bridge (an edge of the induced
 * grid graph whose removal disconnects it) splitting the cells m + m, and E(N): the total
 * number of such bridges.  Usage: halving [-p] [-s] NMAX [JOB NJOBS SPLITDEPTH].  Output lines:
 *   n A(n) H(n) E(n)          (H, E are 0 for odd n)
 * With -p (profile) it also prints, for every n and 1 <= k <= n/2,
 *   B n k B(n,k) G(n,k)
 * where B(n,k) counts bridges whose smaller side has k cells and G(n,k) counts polyominoes
 * having at least one such bridge.
 * With -s (switching) it prints, for every n and 1 <= j <= n-1, statistics of marked triples
 * (P, bridge, side S) with |S| = j, opposite side L:
 *   S n j T O SL SS X
 * T = triples; O = sum of out(P,e,S), the number of moves "delete a leaf c of P in L that is not
 * the bridge end, add a free cell d with exactly one S-neighbour and no neighbour in L - {c}"
 * (each lands on a triple with |S| = j+1, and the reverse move is the same move on the
 * complement-marked triple, so O(n,j) = O(n,n-1-j)); SL = sum of such leaves of S; SS = sum of
 * spots of S (free cells with one S-neighbour, no L-neighbour); X = sum of leaves(L)*spots(S).
 * With NJOBS > 1, subtrees rooted at size SPLITDEPTH are dealt round-robin; job 0 alone
 * counts sizes < SPLITDEPTH (each job counts the subtrees it owns from SPLITDEPTH on), so summing the jobs' outputs gives the totals.
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
static unsigned long long Bp[NMAX + 1][NMAX + 1], Gp[NMAX + 1][NMAX + 1];
static int profile = 0, switching = 0;
static unsigned long long St[NMAX + 1][NMAX + 1], So[NMAX + 1][NMAX + 1],
    Sl[NMAX + 1][NMAX + 1], Ss[NMAX + 1][NMAX + 1], Sx[NMAX + 1][NMAX + 1];
static int bu[NMAX], bv[NMAX], nbridge;
static unsigned int mask;
static unsigned char seen[HGT * W];
static int idxbuf[(HGT + 2) * W], stampbuf[(HGT + 2) * W], stampc;
static int *idx = idxbuf + W;     /* cell -> position in P, or -1; one spare row each side */
static int *stamp = stampbuf + W;
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
            if (low[v] > tin[u]) {
                if (sub[v] == half) nbr++;
                if (switching) { bu[nbridge] = u; bv[nbridge] = v; nbridge++; }
                if (profile) {
                    int k = sub[v] < nP - sub[v] ? sub[v] : nP - sub[v];
                    Bp[nP][k]++;
                    mask |= 1u << k;
                }
            }
        }
    }
}

/* switching statistics for every bridge of the current polyomino (after dfs) */
static void switch_stats(int n) {
    int deg[NMAX], pn[4 * NMAX + 4][4], npn[4 * NMAX + 4], np = 0;
    stampc++;
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        for (int d = 0; d < 4; d++) {
            int c = P[i] + dir[d];
            if (idx[c] >= 0) { deg[i]++; continue; }
            if (stamp[c] != stampc) {
                stamp[c] = stampc; npn[np] = 0;
                for (int e = 0; e < 4; e++) {
                    int q = idx[c + dir[e]];
                    if (q >= 0) pn[np][npn[np]++] = q;
                }
                np++;
            }
        }
    }
    for (int b = 0; b < nbridge; b++) {
        int u = bu[b], v = bv[b], lo = tin[v], hi = tin[v] + sub[v], a = sub[v];
#define INX(i) (tin[i] >= lo && tin[i] < hi)
        unsigned long long lx = 0, ly = 0, sx = 0, sy = 0, ox = 0, oy = 0;
        for (int i = 0; i < n; i++)
            if (deg[i] == 1) { if (INX(i)) lx += i != v; else ly += i != u; }
        for (int p = 0; p < np; p++) {
            int nx = 0, ny = 0, lastx = -1, lasty = -1;
            for (int e = 0; e < npn[p]; e++) {
                int q = pn[p][e];
                if (INX(q)) { nx++; lastx = q; } else { ny++; lasty = q; }
            }
            if (nx == 1 && ny == 0) { sx++; ox += ly; }
            if (nx == 1 && ny == 1 && deg[lasty] == 1 && lasty != u) ox++;
            if (ny == 1 && nx == 0) { sy++; oy += lx; }
            if (ny == 1 && nx == 1 && deg[lastx] == 1 && lastx != v) oy++;
        }
#undef INX
        St[n][a]++; So[n][a] += ox; Sl[n][a] += lx; Ss[n][a] += sx; Sx[n][a] += ly * sx;
        St[n][n - a]++; So[n][n - a] += oy; Sl[n][n - a] += ly; Ss[n][n - a] += sy;
        Sx[n][n - a] += lx * sy;
    }
}

static void record(int n) {
    if (njobs > 1 && n < split && job != 0) return;   /* size == split is counted by its owner */
    A[n]++;
    if (n % 2 && !profile && !switching) return;
    nP = n; half = n % 2 ? -1 : n / 2; nbr = 0; timer_ = 0; mask = 0; nbridge = 0;
    for (int i = 0; i < n; i++) tin[i] = -1;
    dfs(0, -1);
    if (nbr) { Hc[n]++; Ec[n] += nbr; }
    if (switching) switch_stats(n);
    for (int k = 1; mask >> k; k++)
        if (mask >> k & 1u) Gp[n][k]++;
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
    while (argc >= 2 && (strcmp(argv[1], "-p") == 0 || strcmp(argv[1], "-s") == 0)) {
        if (argv[1][1] == 'p') profile = 1; else switching = 1;
        argv++; argc--;
    }
    if (argc < 2) { fprintf(stderr, "usage: halving [-p] [-s] NMAX [JOB NJOBS SPLITDEPTH]\n"); return 2; }
    N = atoi(argv[1]);
    if (N < 1 || N > NMAX) { fprintf(stderr, "NMAX must be in 1..%d\n", NMAX); return 2; }
    if (argc >= 5) { job = atoi(argv[2]); njobs = atoi(argv[3]); split = atoi(argv[4]); }
    for (int i = 0; i < (HGT + 2) * W; i++) idxbuf[i] = -1;
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
    if (profile)
        for (int n = 1; n <= N; n++)
            for (int k = 1; 2 * k <= n; k++)
                printf("B %d %d %llu %llu\n", n, k, Bp[n][k], Gp[n][k]);
    if (switching)
        for (int n = 1; n <= N; n++)
            for (int j = 1; j < n; j++)
                printf("S %d %d %llu %llu %llu %llu %llu\n", n, j, St[n][j], So[n][j], Sl[n][j],
                       Ss[n][j], Sx[n][j]);
    return 0;
}
