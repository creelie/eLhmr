/* indep.c -- branch-and-bound over independent sets of primes (Proposition 2.5 of the Lehmer paper),
 * written independently of independent.py / independent_stream.py.
 *
 * Question: is there an independent set (no element divides another minus 1) of at most K primes of the
 * class Q, with product of p/(p-1) at least V = Vnum/Vden ?   Q = primes >= 5 (mode all), or primes
 * p = 2 (mod 3), p >= 5 (mode mod3).
 *
 * A node S (increasing primes, log-product lp, last element r) has the bound lp + F(m), m = K - |S|,
 * where F(i) is the sum of log(q/(q-1)) over the first i candidates for S (primes q > r of Q with q != 1
 * mod every element of S).  A node with bound < log V - MARGIN is discarded; its children are the
 * candidates c_t, t = 0, 1, ..., with lp + F(t+m) - F(t) >= log V - MARGIN (an initial run, since the
 * child bound decreases in t).  A node with lp >= log V - MARGIN is reported.  Sums are long double
 * (64-bit mantissa); each term log(q/(q-1)) = -log1p(-1/q) carries a relative error below 2^-63 and
 * each addition an absolute error below 2^-63 * (sum) <= 2^-61, so a sum of N terms carries an absolute
 * error below N * 2^-60, i.e. below 1e-9 for N <= 1e9.  MARGIN defaults to 1e-6.
 *
 * usage: indep K Vnum Vden X mode [--margin M] [-v]
 *   X: the candidates are taken among the primes up to X; the program fails loudly if X is too small.
 *   mode all: a table of all primes of Q up to X is kept in memory (X <= 4e9).
 *   mode mod3: the candidates are produced by a segmented sieve of the progression 6j+5 up to X.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef long double ld;
static int K; static ld logV; static ld MARGIN = 1e-6L; static uint64_t X; static int mod3 = 0; static int verbose = 0;
static uint64_t nodes = 0, maxdepth = 0; static uint64_t bydepth[256];
static int found = 0;

/* ---------- base primes and table ---------- */
static uint32_t *base = NULL; static size_t nbase = 0;   /* primes up to sqrt(X)+1 */
static uint32_t *table = NULL; static size_t ntable = 0;  /* mode all: primes of Q up to X */

static void sieve_small(uint64_t lim, uint32_t **out, size_t *n) {
    uint8_t *s = calloc(lim + 1, 1); size_t cnt = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!s[i]) { cnt++; for (uint64_t j = i * i; j <= lim; j += i) s[j] = 1; }
    uint32_t *p = malloc(cnt * sizeof(uint32_t)); size_t k = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!s[i]) p[k++] = (uint32_t)i;
    free(s); *out = p; *n = cnt;
}

/* ---------- candidate stream ---------- */
#define SEG (1u << 20)
typedef struct {
    uint64_t last;            /* produce primes > last */
    /* table mode */
    size_t ti;
    /* sieve mode: progression a + d j */
    uint64_t a, d, j0;        /* current segment starts at j0 */
    uint8_t seg[SEG]; size_t si; int segdone;
} Stream;

static void stream_init(Stream *st, uint64_t last) {
    st->last = last;
    if (!mod3) {
        size_t lo = 0, hi = ntable;
        while (lo < hi) { size_t mid = (lo + hi) / 2; if (table[mid] <= last) lo = mid + 1; else hi = mid; }
        st->ti = lo;
    } else {
        st->a = 5; st->d = 6;
        st->j0 = (last < 5) ? 0 : (last - 5) / 6 + 1;   /* first j with 6j+5 > last */
        st->segdone = 1; st->si = 0;
    }
}

static inline uint64_t mulmod_inv_d(uint64_t p) { /* inverse of 6 mod p, p >= 5 prime */
    /* extended Euclid */
    int64_t t = 0, nt = 1; int64_t r = (int64_t)p, nr = 6 % (int64_t)p;
    while (nr) { int64_t q = r / nr; int64_t tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
    if (t < 0) t += (int64_t)p; return (uint64_t)t;
}

static void fill_segment(Stream *st) {
    memset(st->seg, 1, SEG);
    uint64_t j0 = st->j0, jend = j0 + SEG;                 /* values 6j+5, j in [j0, jend) */
    uint64_t vend = st->a + st->d * (jend - 1);
    for (size_t i = 0; i < nbase; i++) {
        uint64_t p = base[i]; if (p < 5) continue;
        if (p * p > vend) break;
        /* j with 6j+5 = 0 mod p: j = -5 * inv6 mod p */
        uint64_t inv6 = mulmod_inv_d(p);
        uint64_t jp = ((p - 5 % p) % p) * inv6 % p;        /* j = jp mod p */
        /* first j >= j0 with j = jp mod p */
        uint64_t j = j0 + ((jp + p - j0 % p) % p);
        /* exclude the prime p itself: j with 6j+5 = p */
        for (; j < jend; j += p) { uint64_t v = st->a + st->d * j; if (v != p) st->seg[j - j0] = 0; }
    }
    st->si = 0; st->segdone = 0;
}

/* next prime of Q above the current position, or 0 when X is exhausted */
static inline uint64_t stream_next(Stream *st) {
    if (!mod3) {
        if (st->ti >= ntable) return 0;
        return table[st->ti++];
    }
    for (;;) {
        if (st->segdone) {
            if (st->a + st->d * st->j0 > X) return 0;
            fill_segment(st);
        }
        while (st->si < SEG) {
            size_t i = st->si++;
            if (st->seg[i]) { uint64_t v = st->a + st->d * (st->j0 + i); if (v > X) return 0; return v; }
        }
        st->j0 += SEG; st->segdone = 1;
    }
}

/* ---------- the search ---------- */
typedef struct { int depth; uint64_t S[128]; ld lp; } Node;

static Node *stack = NULL; static size_t sp = 0, scap = 0;
static void push(Node *n) { if (sp == scap) { scap = scap ? 2 * scap : 1024; stack = realloc(stack, scap * sizeof(Node)); } stack[sp++] = *n; }

static size_t R = 1u << 16;
static ld *firstlg = NULL, *Fpref = NULL, *accAt = NULL; static uint64_t *firstq = NULL;

static void alloc_R(void) {
    firstlg = realloc(firstlg, R * sizeof(ld)); Fpref = realloc(Fpref, (R + 1) * sizeof(ld));
    accAt = realloc(accAt, R * sizeof(ld)); firstq = realloc(firstq, R * sizeof(uint64_t));
}

static void print_set(Node *n) { printf("["); for (int i = 0; i < n->depth; i++) printf("%s%llu", i ? ", " : "", (unsigned long long)n->S[i]); printf("]"); }

/* process node: returns number of children pushed; -1 if R too small */
static long process(Node *n) {
    int m = K - n->depth;
    if (n->lp >= logV - MARGIN) { found = 1; printf("FOUND (within margin) set of %d primes: ", n->depth); print_set(n); printf("\n"); return 0; }
    if (m == 0) return 0;
    Stream st; stream_init(&st, n->depth ? n->S[n->depth - 1] : 0);
    uint64_t cnt = 0; ld acc = 0; uint64_t need = (uint64_t)m + R;
    Fpref[0] = 0;
    for (;;) {
        uint64_t q = stream_next(&st);
        if (!q) break;
        int ok = 1;
        for (int i = 0; i < n->depth; i++) if (q % n->S[i] == 1) { ok = 0; break; }
        if (!ok) continue;
        ld lg = -log1pl(-1.0L / (ld)q);
        if (cnt < R) { firstlg[cnt] = lg; firstq[cnt] = q; Fpref[cnt + 1] = Fpref[cnt] + lg; }
        acc += lg; cnt++;
        if (cnt >= (uint64_t)m && cnt - m < R) accAt[cnt - m] = acc;
        if (cnt >= need) break;
    }
    if (cnt < (uint64_t)m) { fprintf(stderr, "ERROR: X too small: only %llu candidates for a node of depth %d (m = %d)\n", (unsigned long long)cnt, n->depth, m); exit(2); }
    ld bound = n->lp + accAt[0];
    if (bound < logV - MARGIN) return 0;                       /* pruned */
    if (fabsl(bound - logV) < 10 * MARGIN) printf("   note: node bound within 10*MARGIN of log V: bound - logV = %.3Le\n", bound - logV);
    uint64_t avail = cnt - m;                                   /* accAt[t] known for t < avail */
    long kids = 0; Node c = *n; c.depth = n->depth + 1;
    uint64_t t;
    for (t = 0; t < avail && t < R; t++) {
        ld cb = n->lp + accAt[t] - Fpref[t];
        if (cb < logV - MARGIN) break;
        if (fabsl(cb - logV) < 10 * MARGIN) printf("   note: child bound within 10*MARGIN of log V: cb - logV = %.3Le (q = %llu)\n", cb - logV, (unsigned long long)firstq[t]);
        kids++;
    }
    if (t == avail && t < R) { fprintf(stderr, "ERROR: X too small to decide the children of a node of depth %d\n", n->depth); exit(2); }
    if (t == R) return -1;                                      /* run of children exceeds R */
    for (long s = kids - 1; s >= 0; s--) { c.S[n->depth] = firstq[s]; c.lp = n->lp + firstlg[s]; push(&c); }
    if (verbose && (n->depth <= 1 || nodes % 10000 == 0)) { printf("   node %llu depth %d children %ld stack %zu  S=", (unsigned long long)nodes, n->depth, kids, sp); print_set(n); printf("\n"); fflush(stdout); }
    return kids;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: indep K Vnum Vden X mode(all|mod3) [--margin M] [-v]\n"); return 1; }
    K = atoi(argv[1]); long double Vnum = strtold(argv[2], NULL), Vden = strtold(argv[3], NULL);
    X = strtoull(argv[4], NULL, 10); mod3 = !strcmp(argv[5], "mod3");
    for (int i = 6; i < argc; i++) { if (!strcmp(argv[i], "--margin")) MARGIN = strtold(argv[++i], NULL); else if (!strcmp(argv[i], "-v")) verbose = 1; }
    logV = logl(Vnum) - logl(Vden);
    time_t t0 = time(NULL);
    uint64_t sq = (uint64_t)sqrtl((ld)X) + 2;
    sieve_small(sq, &base, &nbase);
    if (!mod3) {
        if (X > 4000000000ULL) { fprintf(stderr, "mode all needs X <= 4e9\n"); return 1; }
        uint32_t *all; size_t nall; sieve_small(X, &all, &nall);
        table = malloc(nall * sizeof(uint32_t)); ntable = 0;
        for (size_t i = 0; i < nall; i++) if (all[i] >= 5) table[ntable++] = all[i];
        free(all);
    }
    alloc_R();
    memset(bydepth, 0, sizeof bydepth);
    Node root; root.depth = 0; root.lp = 0;
    push(&root);
    while (sp && !found) {
        Node n = stack[--sp];
        nodes++; bydepth[n.depth]++; if ((uint64_t)n.depth > maxdepth) maxdepth = n.depth;
        long r;
        while ((r = process(&n)) < 0) { R *= 2; alloc_R(); fprintf(stderr, "   R doubled to %zu\n", R); }
    }
    printf("K = %d, V = %s/%s (%.12Lf), %s up to %llu, MARGIN %.1Le\n", K, argv[2], argv[3], Vnum / Vden, mod3 ? "primes = 2 mod 3, >= 5" : "primes >= 5", (unsigned long long)X, MARGIN);
    printf("%s\n", found ? "A SET WAS REPORTED (check it exactly)" : "none");
    printf("nodes %llu, max depth %llu, %lld s\n", (unsigned long long)nodes, (unsigned long long)maxdepth, (long long)(time(NULL) - t0));
    printf("nodes by depth:"); for (uint64_t d = 0; d <= maxdepth; d++) printf(" %llu", (unsigned long long)bydepth[d]); printf("\n");
    return found ? 3 : 0;
}
