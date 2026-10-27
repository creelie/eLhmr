/* belowx.c -- all composite solutions of n - 1 = 2 phi(n) with k distinct prime factors, all >= 5, and n < X.
 *
 * The tree of tree_enum.py (Program 2 of the paper) with one extra rule: at a node with prefix product A, last
 * prime r and m primes still to choose, every remaining prime is at least lo (the lower end of the interval
 * for the next prime), so n >= A lo^m; the node is discarded when A lo^m >= X, and the interval for the next
 * prime is cut at floor((X/A)^(1/m)).  At m = 2 the prime p is enumerated over its interval and the last
 * prime is read off: t = C p - 2B must divide A p - 1, and q = 1 + (A p - 1)/t must be a prime > p.
 * Nothing is factored.  Every bound is computed exactly in integers (GMP), from a floating-point guess.
 *
 * usage: belowx X k [--part i/P] [-v]      X as a decimal integer (e.g. 1e40 is not accepted; write the digits)
 * With --part i/P only every P-th node created at depth --splitdepth + 1 (default 9), counted in creation order, starting from the i-th, is searched (for parallel runs).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <gmp.h>

static mpz_t X; static int K; static int verbose = 0; static int part = 0, nparts = 1, splitdepth = 8; static unsigned long long gcount = 0;
static long EA = 2, EB = 1, EPS = -1, PMIN = 5;   /* equation EB (n + EPS) = EA phi(n), primes >= PMIN */
static unsigned long long nodes = 0, leaves = 0, ptested = 0, divhits = 0, sols = 0, cut = 0;
static unsigned long long maxrange = 0;

/* base primes for segmented sieving up to 2^32 */
static uint32_t *base; static size_t nbase; static const uint64_t BASEMAX = 1u << 26;
static void sieve_small(uint64_t lim, uint32_t **out, size_t *n) {
    uint8_t *s = calloc(lim + 1, 1); size_t cnt = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!s[i]) { cnt++; for (uint64_t j = i * i; j <= lim; j += i) s[j] = 1; }
    uint32_t *p = malloc(cnt * sizeof(uint32_t)); size_t k = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!s[i]) p[k++] = (uint32_t)i;
    free(s); *out = p; *n = cnt;
}
/* primes in [lo, hi], hi < 2^62, delivered to a callback; segmented sieve of odd numbers */
#define SEG (1u << 20)
static uint8_t segbuf[SEG];
typedef void (*prime_cb)(uint64_t p, void *ctx);
static void primes_between(uint64_t lo, uint64_t hi, prime_cb cb, void *ctx) {
    if (lo < 3) lo = 3;
    if (lo % 2 == 0) lo++;
    for (uint64_t start = lo; start <= hi; start += 2ULL * SEG) {       /* odd numbers start + 2i */
        uint64_t end = start + 2ULL * (SEG - 1); if (end > hi) end = hi;
        if (end > BASEMAX * BASEMAX) { fprintf(stderr, "interval end %llu beyond the base primes\n", (unsigned long long)end); exit(2); }
        size_t len = (size_t)((end - start) / 2 + 1);
        memset(segbuf, 1, len);
        for (size_t i = 0; i < nbase; i++) {
            uint64_t p = base[i]; if (p == 2) continue;
            if (p * p > end) break;
            uint64_t j = ((start + p - 1) / p) * p; if (j < p * p) j = p * p; if (j % 2 == 0) j += p;
            for (; j <= end; j += 2 * p) segbuf[(j - start) / 2] = 0;
        }
        for (size_t i = 0; i < len; i++) if (segbuf[i]) cb(start + 2 * i, ctx);
    }
}

/* exact bounds -------------------------------------------------------- */
static mpz_t t1, t2, t3, t4;
/* largest p with p^m * Tden > (p-1)^m * Tnum  (i.e. (p/(p-1))^m > Tnum/Tden) */
static int cond_upper(uint64_t p, int m, mpz_t Tnum, mpz_t Tden) {
    mpz_set_ui(t1, p); mpz_pow_ui(t1, t1, m); mpz_mul(t1, t1, Tden);
    mpz_set_ui(t2, p - 1); mpz_pow_ui(t2, t2, m); mpz_mul(t2, t2, Tnum);
    return mpz_cmp(t1, t2) > 0;
}
static uint64_t exact_upper(mpz_t Tnum, mpz_t Tden, int m) {
    double T = mpz_get_d(Tnum) / mpz_get_d(Tden);
    double g0 = 1.0 / (1.0 - pow(T, -1.0 / m)) + 2;
    if (g0 > 4e18) g0 = 4e18;
    uint64_t g = (uint64_t)g0; if (g < 3) g = 3;
    while (g > 2 && !cond_upper(g, m, Tnum, Tden)) g--;
    while (cond_upper(g + 1, m, Tnum, Tden)) g++;
    return g;
}
static int cond_upper_ge(uint64_t p, int m, mpz_t Tnum, mpz_t Tden) {
    mpz_set_ui(t1, p); mpz_pow_ui(t1, t1, m); mpz_mul(t1, t1, Tden);
    mpz_set_ui(t2, p - 1); mpz_pow_ui(t2, t2, m); mpz_mul(t2, t2, Tnum);
    return mpz_cmp(t1, t2) >= 0;
}
static uint64_t exact_upper_ge(mpz_t Tnum, mpz_t Tden, int m) {   /* largest p with (p/(p-1))^m >= Tnum/Tden > 1 */
    double T = mpz_get_d(Tnum) / mpz_get_d(Tden);
    double g0 = 1.0 / (1.0 - pow(T, -1.0 / m)) + 2;
    if (g0 > 4e18) g0 = 4e18;
    uint64_t g = (uint64_t)g0; if (g < 3) g = 3;
    while (g > 2 && !cond_upper_ge(g, m, Tnum, Tden)) g--;
    while (cond_upper_ge(g + 1, m, Tnum, Tden)) g++;
    return g;
}
/* smallest p >= 2 with p * den < (p-1) * num   (num > den > 0) */
static int cond_lower(uint64_t p, mpz_t num, mpz_t den) {
    mpz_mul_ui(t1, den, p); mpz_mul_ui(t2, num, p - 1); return mpz_cmp(t1, t2) < 0;
}
static uint64_t exact_lower(mpz_t num, mpz_t den) {
    mpz_sub(t3, num, den); mpz_fdiv_q(t4, num, t3);
    uint64_t p = mpz_get_ui(t4) + 1;
    while (!cond_lower(p, num, den)) p++;
    while (p - 1 >= 2 && cond_lower(p - 1, num, den)) p--;
    return p;
}

/* the search ------------------------------------------------------------ */
typedef struct { int depth; uint64_t S[64]; mpz_t A, B; } Node;
static Node *stack; static size_t sp = 0, scap = 0;
static void push(int depth, uint64_t *S, mpz_t A, mpz_t B) {
    if (sp == scap) { size_t old = scap; scap = scap ? 2 * scap : 256; stack = realloc(stack, scap * sizeof(Node)); for (size_t i = old; i < scap; i++) { mpz_init(stack[i].A); mpz_init(stack[i].B); } }
    stack[sp].depth = depth; memcpy(stack[sp].S, S, depth * sizeof(uint64_t)); mpz_set(stack[sp].A, A); mpz_set(stack[sp].B, B); sp++;
}

typedef struct { Node *n; mpz_t C, twoB; uint64_t *kids; size_t nk, kcap; } Ctx;
static mpz_t tt, num, q, nn, ph;

static int indep_ok(uint64_t p, Node *n) { for (int i = 0; i < n->depth; i++) if (p % n->S[i] == 1) return 0; return 1; }

static void leaf_cb(uint64_t p, void *vc) {
    Ctx *c = vc; Node *n = c->n;
    if (!indep_ok(p, n)) return;
    ptested++;
    mpz_mul_ui(tt, c->C, p); mpz_sub(tt, tt, c->twoB);              /* t = C p - aB */
    if (mpz_sgn(tt) <= 0) return;
    mpz_mul_ui(num, n->A, p); if (EPS < 0) mpz_sub_ui(num, num, 1); else mpz_add_ui(num, num, 1); mpz_mul_ui(num, num, EB);   /* b (A p + eps) */
    if (!mpz_divisible_p(num, tt)) return;
    divhits++;
    mpz_divexact(q, num, tt); mpz_add_ui(q, q, 1);                   /* q = 1 + (Ap-1)/t */
    if (mpz_cmp_ui(q, p) <= 0) return;
    if (!mpz_probab_prime_p(q, 40)) return;
    for (int i = 0; i < n->depth; i++) { mpz_sub_ui(t1, q, 1); if (mpz_divisible_ui_p(t1, n->S[i])) return; }
    mpz_sub_ui(t1, q, 1); if (mpz_divisible_ui_p(t1, p)) return;
    mpz_mul_ui(nn, n->A, p); mpz_mul(nn, nn, q);
    mpz_mul_ui(ph, n->B, p - 1); mpz_sub_ui(t1, q, 1); mpz_mul(ph, ph, t1); mpz_mul_ui(ph, ph, EA);
    if (EPS < 0) mpz_sub_ui(t2, nn, 1); else mpz_add_ui(t2, nn, 1); mpz_mul_ui(t2, t2, EB);
    if (mpz_cmp(t2, ph) == 0) { sols++; gmp_printf("SOLUTION n = %Zd, primes ", nn); for (int i = 0; i < n->depth; i++) printf("%llu ", (unsigned long long)n->S[i]); gmp_printf("%llu %Zd\n", (unsigned long long)p, q); fflush(stdout); }
}
static void child_cb(uint64_t p, void *vc) {
    Ctx *c = vc; if (!indep_ok(p, c->n)) return;
    if (c->nk == c->kcap) { c->kcap = c->kcap ? 2 * c->kcap : 1024; c->kids = realloc(c->kids, c->kcap * sizeof(uint64_t)); }
    c->kids[c->nk++] = p;
}

static mpz_t Tnum, Tden, W, lonum, loden, XA, cap;

static void process(Node *n) {
    int j = n->depth, m = K - j;
    nodes++;
    if (verbose && nodes % 100000 == 0) { fprintf(stderr, "   nodes %llu leaves %llu ptested %llu cuts %llu depth %d\n", nodes, leaves, ptested, cut, j); }
    /* P = A/B < 2 required */
    mpz_mul_ui(t1, n->B, EA); mpz_mul_ui(t2, n->A, EB); if (mpz_cmp(t2, t1) >= 0) return;
    uint64_t pj = j ? n->S[j - 1] : 1;
    /* hi: (p/(p-1))^m > 2B/A ; lo: p/(p-1) < (2BW+1)/(AW), W = (pj+1)^m */
    mpz_mul_ui(Tnum, n->B, EA); mpz_mul_ui(Tden, n->A, EB);
    mpz_set_ui(W, pj + 1); mpz_pow_ui(W, W, m);
    uint64_t hi, lo;
    if (EPS < 0) {
        hi = exact_upper(Tnum, Tden, m);
        mpz_mul(lonum, Tnum, W); mpz_add_ui(lonum, lonum, EB); mpz_mul(loden, Tden, W);
        lo = exact_lower(lonum, loden);
    } else {
        mpz_mul(lonum, Tnum, W); mpz_sub_ui(lonum, lonum, EB); mpz_mul(loden, Tden, W);
        hi = exact_upper_ge(lonum, loden, m);
        lo = exact_lower(Tnum, Tden);
    }
    if (lo < pj + 1) lo = pj + 1; if (lo < (uint64_t)PMIN) lo = PMIN;
    /* size: A lo^m < X, and p <= (X/A)^(1/m) */
    mpz_set_ui(t1, lo); mpz_pow_ui(t1, t1, m); mpz_mul(t1, t1, n->A);
    if (mpz_cmp(t1, X) >= 0) { cut++; return; }
    mpz_fdiv_q(XA, X, n->A); mpz_root(cap, XA, m);
    if (mpz_fits_ulong_p(cap)) { uint64_t cp = mpz_get_ui(cap); if (cp < hi) hi = cp; }
    if (hi < lo) return;
    if (hi >= (1ULL << 62)) { fprintf(stderr, "interval too large at depth %d\n", j); exit(2); }
    Ctx c; c.n = n; mpz_init(c.C); mpz_init(c.twoB); c.kids = NULL; c.nk = c.kcap = 0;
    if (m == 2) {
        leaves++; if (hi - lo > maxrange) maxrange = hi - lo;
        mpz_mul_ui(c.twoB, n->B, EA); mpz_mul_ui(t1, n->A, EB); mpz_sub(c.C, c.twoB, t1);
        if (mpz_sgn(c.C) > 0) primes_between(lo, hi, leaf_cb, &c);
        mpz_clear(c.C); mpz_clear(c.twoB); return;
    }
    primes_between(lo, hi, child_cb, &c);
    for (size_t s = c.nk; s-- > 0;) {
        if (j == splitdepth && (long)(gcount++ % nparts) != part) continue;
        uint64_t p = c.kids[s];
        mpz_mul_ui(t1, n->A, p); mpz_mul_ui(t2, n->B, p - 1);
        uint64_t S[64]; memcpy(S, n->S, j * sizeof(uint64_t)); S[j] = p;
        push(j + 1, S, t1, t2);
    }
    if (verbose && j <= 1) { printf("   depth %d node (", j); for (int i = 0; i < j; i++) printf("%llu ", (unsigned long long)n->S[i]); printf(") lo %llu hi %llu children %zu\n", (unsigned long long)lo, (unsigned long long)hi, c.nk); fflush(stdout); }
    free(c.kids); mpz_clear(c.C); mpz_clear(c.twoB);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: belowx X k [--part i/P] [-v]\n"); return 1; }
    mpz_init_set_str(X, argv[1], 10); K = atoi(argv[2]);
    for (int i = 3; i < argc; i++) { if (!strcmp(argv[i], "--part")) sscanf(argv[++i], "%d/%d", &part, &nparts); else if (!strcmp(argv[i], "-v")) verbose = 1; else if (!strcmp(argv[i], "--splitdepth")) splitdepth = atoi(argv[++i]); else if (!strcmp(argv[i], "--eq")) sscanf(argv[++i], "%ld,%ld,%ld,%ld", &EA, &EB, &EPS, &PMIN); }
    mpz_inits(t1, t2, t3, t4, tt, num, q, nn, ph, Tnum, Tden, W, lonum, loden, XA, cap, NULL);
    sieve_small(BASEMAX, &base, &nbase);        /* primes to BASEMAX: intervals up to BASEMAX^2, checked in primes_between */
    time_t t0 = time(NULL);
    mpz_t one; mpz_init_set_ui(one, 1); uint64_t S0[64];
    push(0, S0, one, one);
    while (sp) { Node *n = &stack[--sp]; Node cur; cur.depth = n->depth; memcpy(cur.S, n->S, n->depth * sizeof(uint64_t)); mpz_init_set(cur.A, n->A); mpz_init_set(cur.B, n->B); process(&cur); mpz_clear(cur.A); mpz_clear(cur.B); }
    gmp_printf("eq %ld(n%+ld) = %ld phi, pmin %ld; X = %Zd, k = %d, part %d/%d: nodes %llu, size cuts %llu, leaves %llu, max interval %llu, p tested %llu, divisibility hits %llu, solutions %llu, %lld s\n",
        EB, EPS, EA, PMIN, X, K, part, nparts, nodes, cut, leaves, maxrange, ptested, divhits, sols, (long long)(time(NULL) - t0));
    return 0;
}
