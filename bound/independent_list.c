/* indep2.c -- the search of indep.c (mode all: primes >= 5, table in memory) with candidate lists passed
 * down the tree: the candidates of a child S + {q} are the candidates of S above q that are not 1 mod q,
 * so each node filters its parent's list with one modulus instead of rescanning the prime table.
 * Lists are kept at length up to LCAP = 2m + 256; a list that becomes too short for its node is rebuilt
 * from the prime table.  Same bounds, same MARGIN rule, same output as indep.c.
 * usage: indep2 K Vnum Vden X [--margin M] [-v]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
typedef long double ld;
static int K; static ld logV, MARGIN = 1e-6L; static uint64_t X; static int verbose = 0, found = 0;
static uint64_t nodes = 0, maxdepth = 0, bydepth[256], rebuilds = 0;
static uint32_t *table; static size_t ntable;
static ld *LG;   /* LG[i] = log(table[i]/(table[i]-1)) */
#define MAXD 200
static uint32_t *cand[MAXD]; static ld *pref[MAXD]; static size_t LCAP;
static uint64_t S[MAXD];

static void print_set(int d) { printf("["); for (int i = 0; i < d; i++) printf("%s%llu", i ? ", " : "", (unsigned long long)S[i]); printf("]"); }

/* rebuild the candidate list for the node S[0..d) (last prime r) from the table: indices of primes > r not 1 mod any S */
static size_t rebuild(int d, uint64_t r, uint32_t *out) {
    rebuilds++;
    size_t lo = 0, hi = ntable; while (lo < hi) { size_t mid = (lo + hi) / 2; if (table[mid] <= r) lo = mid + 1; else hi = mid; }
    size_t n = 0;
    for (size_t i = lo; i < ntable && n < LCAP; i++) { uint32_t q = table[i]; int ok = 1; for (int j = 0; j < d; j++) if (q % S[j] == 1) { ok = 0; break; } if (ok) out[n++] = (uint32_t)i; }
    return n;
}

static void rec(int d, ld lp, size_t nc) {
    nodes++; bydepth[d]++; if ((uint64_t)d > maxdepth) maxdepth = d;
    if (lp >= logV - MARGIN) { found = 1; printf("FOUND (within margin) set of %d primes: ", d); print_set(d); printf("\n"); return; }
    int m = K - d; if (m == 0) return;
    uint32_t *c = cand[d]; ld *F = pref[d];
    if (nc < (size_t)m + 1) { nc = rebuild(d, d ? S[d - 1] : 0, c); if (nc < (size_t)m + 1) { fprintf(stderr, "ERROR: X too small at depth %d\n", d); exit(2); } }
    F[0] = 0; for (size_t i = 0; i < nc; i++) F[i + 1] = F[i] + LG[c[i]];
    ld bound = lp + F[m];
    if (bound < logV - MARGIN) return;
    if (fabsl(bound - logV) < 10 * MARGIN) printf("   note: node bound within 10*MARGIN of log V: %.3Le\n", bound - logV);
    size_t t; size_t nk = 0;
    for (t = 0; t + m < nc; t++) { ld cb = lp + F[t + m] - F[t]; if (cb < logV - MARGIN) break; if (fabsl(cb - logV) < 10 * MARGIN) printf("   note: child bound within 10*MARGIN of log V: %.3Le (q = %u)\n", cb - logV, table[c[t]]); nk++; }
    if (t + m >= nc) {   /* list exhausted before the run of children ended: rebuild a full list and retry */
        size_t n2 = rebuild(d, d ? S[d - 1] : 0, c);
        if (n2 <= nc) { fprintf(stderr, "ERROR: X too small to decide the children at depth %d\n", d); exit(2); }
        rec_again: ; nodes--; bydepth[d]--; rec(d, lp, n2); return;
    }
    if (verbose && (d <= 1 || nodes % 100000 == 0)) { printf("   node %llu depth %d children %zu S=", (unsigned long long)nodes, d, nk); print_set(d); printf("\n"); fflush(stdout); }
    for (size_t s = 0; s < nk && !found; s++) {
        uint32_t q = table[c[s]]; S[d] = q;
        uint32_t *cc = cand[d + 1]; size_t n2 = 0;
        for (size_t i = s + 1; i < nc && n2 < LCAP; i++) if (table[c[i]] % q != 1) cc[n2++] = c[i];
        rec(d + 1, lp + LG[c[s]], n2);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: indep2 K Vnum Vden X [--margin M] [-v]\n"); return 1; }
    K = atoi(argv[1]); ld Vnum = strtold(argv[2], NULL), Vden = strtold(argv[3], NULL); X = strtoull(argv[4], NULL, 10);
    for (int i = 5; i < argc; i++) { if (!strcmp(argv[i], "--margin")) MARGIN = strtold(argv[++i], NULL); else if (!strcmp(argv[i], "-v")) verbose = 1; }
    logV = logl(Vnum) - logl(Vden);
    time_t t0 = time(NULL);
    uint8_t *s = calloc(X + 1, 1); size_t cnt = 0;
    for (uint64_t i = 2; i <= X; i++) if (!s[i]) { if (i >= 5) cnt++; for (uint64_t j = i * i; j <= X; j += i) s[j] = 1; }
    table = malloc(cnt * sizeof(uint32_t)); LG = malloc(cnt * sizeof(ld)); ntable = 0;
    for (uint64_t i = 5; i <= X; i++) if (!s[i]) { table[ntable] = (uint32_t)i; LG[ntable] = -log1pl(-1.0L / (ld)i); ntable++; }
    free(s);
    LCAP = 2 * (size_t)K + 256;
    for (int d = 0; d < MAXD; d++) { cand[d] = malloc(LCAP * sizeof(uint32_t)); pref[d] = malloc((LCAP + 1) * sizeof(ld)); }
    memset(bydepth, 0, sizeof bydepth);
    rec(0, 0, 0);
    printf("K = %d, V = %s/%s (%.12Lf), primes >= 5 up to %llu, MARGIN %.1Le\n", K, argv[2], argv[3], Vnum / Vden, (unsigned long long)X, MARGIN);
    printf("%s\n", found ? "A SET WAS REPORTED (check it exactly)" : "none");
    printf("nodes %llu, max depth %llu, list rebuilds %llu, %lld s\n", (unsigned long long)nodes, (unsigned long long)maxdepth, (unsigned long long)rebuilds, (long long)(time(NULL) - t0));
    printf("nodes by depth:"); for (uint64_t d = 0; d <= maxdepth; d++) printf(" %llu", (unsigned long long)bydepth[d]); printf("\n");
    return found ? 3 : 0;
}
