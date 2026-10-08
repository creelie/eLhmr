/*
 scan3.c -- the last three entries of

        A x p q + eps = 2 B (x - 1)(p - 1)(q - 1),        x < p < q,                                    (*)

 for every admissible x in an interval, where A = x_1 ... x_j and B = (x_1 - 1) ... (x_j - 1) are fixed.

 For fixed x put A' = A x, B' = B (x - 1), c = 2B' - A' and N = 2A'B' + eps c.  If c <= 0 there is nothing to do.
 Otherwise t = c p - 2B' is a divisor of N with 1 <= t <= sqrt N and t = -2B' (mod c), and q - 1 = (A'p + eps)/t.
 With sigma = p + q and pi = p q,

        c pi = 2B' sigma - 2B' + eps,          (q - p)^2 = sigma^2 - 4 pi,

 so sigma lies in one class modulo c.  The divisors are split at a value t_d:

   - t < t_d by trial division: p runs over the integers with c(x+2) - 2B' <= cp - 2B' < t_d, and p is accepted
     when t = cp - 2B' divides A'p + eps;
   - t_d <= t <= sqrt N by the sum of the two factors: since t + N/t = c sigma - 4B' decreases in t on (0, sqrt N],
     sigma runs over its class in  (2 sqrt N + 4B')/c <= sigma <= (t_d + N/t_d + 4B')/c,  and sigma^2 - 4 pi is
     tested for being a square.

 t_d is chosen to minimise the estimated work.  When that work exceeds a threshold, x is not treated here but reported
 on an 'F' line; the caller then factors N completely and reads off its divisors in the class.  Quantities that fit
 in 128 bits are handled in machine arithmetic; beyond that the trial division tests whether t < 2^64 divides N
 (equivalent to t | A'p + eps, since c (A'p + eps) = A't + N and gcd(t, c) = gcd(2B', A') = 1) and the sums use GMP.

 Both loops are filtered by congruences modulo small primes l that every completion in the class of entries under
 consideration satisfies.  Each of p and q lies in an allowed set of residues modulo l (below).  Since p and q are
 the roots of X^2 - sigma X + pi, the pair (sigma, pi) must give modulo l a polynomial with a root, all of whose
 roots are allowed; and sigma^2 - 4 pi must be a square modulo 256, 9, 25 and 49.  Moreover sigma is even, and
 sigma = 1 (mod 3) when p and q are both 2 mod 3.  The sums use a modulus only when the exact tests it saves cost more
 than its table.  The trial division skips the p that are not allowed modulo the primes up to 61.  A candidate that
 passes the filters is tested exactly, and every completion is verified with GMP before it is printed.

   mode 0 (primes):  x runs over the primes in [lo, hi] with x != 1 mod x_i for all i.  The entries p, q are taken
                     to be primes larger than x with p, q != 1 mod x_i: they are odd, prime to every prime l < lo,
                     and equal to 2 mod 3 if 3 | A (Lemma 2.2).
   mode 1 (integers prime to 3):  x runs over the odd integers in [lo, hi] with x != 0 mod 3, x != 0 mod r for the
                     listed primes r of B (list R0) and x != 1 mod r for the listed primes r of A (list R1); p and q
                     are taken to satisfy the same conditions, which follow from gcd(x_i, x_j - 1) = 1.
   mode 2 (odd integers):  as mode 1 without the conditions modulo 3 (used for the tests).

 Input lines:   eps mode j x_1 ... x_j lo hi [n0 r_1 .. r_n0 n1 r_1 .. r_n1]      (the lists only in mode 1)
 Output:        "S x_1 .. x_j x p q"   for each completion (p and q integers, not necessarily prime)
                "F x_1 .. x_j x"       for each x left to the caller
                "T nx nempty ntd nsig nsurv nfound ndef sec"   once per input line: admissible x, x with an empty
                range, trial divisions, values of sigma, candidates tested exactly, completions, deferred x, seconds.
 Options:       scan3 [a1 a2 fcost [forcetd]]   estimated cost in ns of one value of p in the trial division and
                of one value of sigma, and the threshold (ns) above which x is deferred (defaults 1.0, 0.11, 4e6).
                forcetd = 1 puts every divisor into the trial division, forcetd = 2 every divisor into the sum
                route, forcetd = 3 uses the wide paths below for every x (for testing).
 Build:         gcc -O3 -march=native -o scan3 scan3.c -lgmp -lm
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <gmp.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;
typedef __int128 i128;

static double A1 = 1.0, A2 = 0.11, FCOST = 4e6;
static int FORCE = 0;

/* ---------------------------------------------------------------- allowed residues */
#define LMAX 64
static unsigned char allowed[LMAX][LMAX];       /* allowed[l][y]: p and q may be y modulo the prime l */
static unsigned char active[LMAX];              /* some residue modulo l is excluded */
static unsigned char rootok[LMAX][LMAX][LMAX];  /* rootok[l][sigma][pi] */

static int is_small_prime(int l) { if (l < 2) return 0; for (int d = 2; d * d <= l; d++) if (l % d == 0) return 0; return 1; }

#define NSUM 14
static const int SUMMOD[NSUM] = {256, 9, 25, 49, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43};
static const int SUMPR[NSUM]  = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43};
static unsigned char issq[NSUM][256];
static u64 SW[NSUM][256];

#define NWH 18
static const int WHMOD[NWH] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
static u64 WW[NWH][64];
static int nwh; static int whm[NWH];

static void build_windows(const unsigned char *ok, int l, u64 *W) {
    u64 rep[(256 + 64) / 64 + 2];
    memset(rep, 0, sizeof rep);
    for (int i = 0, r = 0; i < l + 64; i++) { if (ok[r]) rep[i >> 6] |= 1ULL << (i & 63); if (++r == l) r = 0; }
    for (int j = 0; j < l; j++) {
        int w = j >> 6, b = j & 63;
        W[j] = b ? (rep[w] >> b) | (rep[w + 1] << (64 - b)) : rep[w];
    }
}

/* the window of allowed steps k for the sums modulo l = SUMMOD[m], where sigma = sm + k hm and pi = pm + k gm (mod l):
   sigma^2 - 4 pi is a square modulo l and X^2 - sigma X + pi has a root, all of whose roots are allowed */
static unsigned char sqm[NSUM][256], rpr[NSUM][256];
static void sum_windows(int m, u64 sm, u64 hm, u64 pm, u64 gm) {
    int l = SUMMOD[m], pr = SUMPR[m];
    unsigned char okk[256];
    unsigned s2 = (unsigned) sm, p2 = (unsigned) pm, h2 = (unsigned) hm, g2 = (unsigned) gm;
    unsigned f2 = (unsigned) ((4 * pm) % l), e2 = (unsigned) ((4 * gm) % l);          /* 4 pi mod l */
    for (int k = 0; k < l; k++) {
        int D2 = (int) sqm[m][s2] - (int) f2; if (D2 < 0) D2 += l;
        okk[k] = issq[m][D2] && rootok[pr][rpr[m][s2]][rpr[m][p2]];
        s2 += h2; if (s2 >= (unsigned) l) s2 -= l;
        p2 += g2; if (p2 >= (unsigned) l) p2 -= l;
        f2 += e2; if (f2 >= (unsigned) l) f2 -= l;
    }
    build_windows(okk, l, SW[m]);
}

/* The moduli worth sieving the sums with: modulus m is used when the exact tests it is expected to save (survivors
   times the fraction it removes, SUMDENS being a rough fraction that passes) cost more than building its window.
   The window of an unused modulus lets every step pass.  Returns the number of moduli used. */
static const double SUMDENS[NSUM] = {0.2, 0.45, 0.45, 0.45, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5};
static unsigned char sw_open[NSUM];
static int sum_moduli(double nk, double ctest, int *use) {
    double S = nk; int nu = 0;
    for (int m = 0; m < NSUM; m++) {
        use[m] = S * (1 - SUMDENS[m]) * ctest > 3.5 * SUMMOD[m];
        if (use[m]) { S *= SUMDENS[m]; nu++; sw_open[m] = 0; }
        else if (!sw_open[m]) { for (int i = 0; i < SUMMOD[m]; i++) SW[m][i] = ~0ULL; sw_open[m] = 1; }
    }
    return nu;
}

static int three_all;   /* p and q are 2 mod 3 */

static void setup_task(int mode, int j, const u64 *xs, u64 lo, int n0, const u64 *R0, int n1, const u64 *R1) {
    memset(active, 0, sizeof active);
    memset(allowed, 1, sizeof allowed);
    three_all = 0;
    for (int l = 2; l < LMAX; l++) {
        if (!is_small_prime(l)) continue;
        if (l == 2) { allowed[2][0] = 0; active[2] = 1; continue; }
        if (mode == 0) {
            if ((u64) l < lo) { allowed[l][0] = 0; active[l] = 1; }
            for (int i = 0; i < j; i++) if (xs[i] == (u64) l) { allowed[l][1] = 0; active[l] = 1; }
            if (l == 3) for (int i = 0; i < j; i++) if (xs[i] == 3) { allowed[3][0] = allowed[3][1] = 0; active[3] = 1; three_all = 1; }
        } else {
            if (l == 3 && mode == 1) { allowed[3][0] = 0; active[3] = 1; }
            for (int i = 0; i < n0; i++) if (R0[i] == (u64) l) { allowed[l][0] = 0; active[l] = 1; }
            for (int i = 0; i < n1; i++) if (R1[i] == (u64) l) { allowed[l][1] = 0; active[l] = 1; }
        }
    }
    for (int l = 2; l < LMAX; l++) {
        if (!is_small_prime(l)) continue;
        for (int s = 0; s < l; s++) for (int pi = 0; pi < l; pi++) {
            int nr = 0, ok = 1;
            for (int y = 0; y < l; y++) if (((y * y - s * y + pi) % l + l) % l == 0) { nr++; if (!allowed[l][y]) ok = 0; }
            rootok[l][s][pi] = (nr > 0 && ok);
        }
    }
    for (int m = 0; m < NSUM; m++) {
        int l = SUMMOD[m]; memset(issq[m], 0, 256);
        for (int y = 0; y < l; y++) issq[m][(y * y) % l] = 1;
        for (int y = 0; y < l; y++) { sqm[m][y] = (unsigned char) ((y * y) % l); rpr[m][y] = (unsigned char) (y % SUMPR[m]); }
    }
    nwh = 0;
    for (int m = 0; m < NWH; m++) {
        int l = WHMOD[m]; unsigned char ok[64];
        for (int y = 0; y < l; y++) ok[y] = allowed[l][y];
        build_windows(ok, l, WW[m]);
        if (active[l]) whm[nwh++] = m;
    }
}

/* ---------------------------------------------------------------- helpers */
static char prefix_str[1 << 14];
static long nfound, ndef, nsurv, nempty;
static double ntd, nsig;
static mpz_t A, B, Ap, Bp, c, N, sN, tmin, tmp, tmp2, pz, qz, td, sig, cls, inv;

static int u128_str(u128 v, char *buf) {
    char t[48]; int n = 0;
    if (v == 0) t[n++] = '0';
    while (v) { t[n++] = '0' + (int) (v % 10); v /= 10; }
    for (int i = 0; i < n; i++) buf[i] = t[n - 1 - i];
    buf[n] = 0; return n;
}
static void mpz_set_u128(mpz_t z, u128 v) { u64 w[2] = {(u64) v, (u64) (v >> 64)}; mpz_import(z, 2, -1, 8, 0, 0, w); }
static u128 mpz_get_u128(const mpz_t z) {          /* z >= 0, z < 2^128 */
    u64 w[2] = {0, 0}; size_t cnt = 0;
    mpz_export(w, &cnt, -1, 8, 0, 0, z);
    return ((u128) w[1] << 64) | w[0];
}
static int fits(const mpz_t z, int bits) { return mpz_sgn(z) >= 0 && mpz_sizeinbase(z, 2) <= (size_t) bits; }
static inline u64 mod128(u128 v, u64 l) {
    u64 t64 = (~0ULL % l + 1) % l;
    return (u64) ((((u128) ((u64) (v >> 64) % l)) * t64 + ((u64) v % l)) % l);
}
/* X mod t; one hardware division when t < 2^64 */
static inline u128 mod128_by(u128 X, u128 t) {
    if ((t >> 64) == 0) {
        u64 d = (u64) t, hi = (u64) (X >> 64), lo = (u64) X, q, r;
        if (hi >= d) hi %= d;
        __asm__("divq %4" : "=a"(q), "=d"(r) : "a"(lo), "d"(hi), "rm"(d));
        (void) q;
        return r;
    }
    return X % t;
}
static inline u128 isqrt128(u128 D) {
    u128 e = (u128) sqrtl((long double) D);
    while (e * e > D) e--;
    while ((e + 1) * (e + 1) <= D) e++;
    return e;
}

/* exact check of (*) and output */
static void report(u64 x, u128 p, u128 q, int eps) {
    char bp[48], bq[48]; u128_str(p, bp); u128_str(q, bq);
    mpz_set_u128(pz, p); mpz_set_u128(qz, q);
    mpz_mul(tmp, Ap, pz); mpz_mul(tmp, tmp, qz); if (eps > 0) mpz_add_ui(tmp, tmp, 1); else mpz_sub_ui(tmp, tmp, 1);
    mpz_sub_ui(pz, pz, 1); mpz_sub_ui(qz, qz, 1);
    mpz_mul(tmp2, Bp, pz); mpz_mul(tmp2, tmp2, qz); mpz_mul_2exp(tmp2, tmp2, 1);
    if (mpz_cmp(tmp, tmp2) != 0 || !(p > x) || !(q > p)) {
        fprintf(stderr, "scan3: false completion %s %llu %s %s\n", prefix_str, (unsigned long long) x, bp, bq); exit(3);
    }
    printf("S %s %llu %s %s\n", prefix_str, (unsigned long long) x, bp, bq);
    nfound++;
}

/* the same for p, q given as integers of any size */
static mpz_t R1, R2, R3;
static void report_mpz(u64 x, const mpz_t p, const mpz_t q, int eps) {
    mpz_mul(R1, Ap, p); mpz_mul(R1, R1, q); if (eps > 0) mpz_add_ui(R1, R1, 1); else mpz_sub_ui(R1, R1, 1);
    mpz_sub_ui(R2, p, 1); mpz_sub_ui(R3, q, 1);
    mpz_mul(R2, R2, R3); mpz_mul(R2, R2, Bp); mpz_mul_2exp(R2, R2, 1);
    if (mpz_cmp(R1, R2) != 0 || mpz_cmp_ui(p, x) <= 0 || mpz_cmp(q, p) <= 0) {
        gmp_fprintf(stderr, "scan3: false completion %s %llu %Zd %Zd\n", prefix_str, (unsigned long long) x, p, q); exit(3);
    }
    gmp_printf("S %s %llu %Zd %Zd\n", prefix_str, (unsigned long long) x, p, q);
    nfound++;
}

/* trial division in the wide path: t divides A'P + eps; then q = 1 + (A'P + eps)/t */
static mpz_t W1, W2;
static void trial_hit_wide(u64 x, u64 P, int eps) {
    mpz_set_ui(W1, P); mpz_mul(W2, Ap, W1); if (eps > 0) mpz_add_ui(W2, W2, 1); else mpz_sub_ui(W2, W2, 1);
    mpz_mul_ui(R1, c, P); mpz_mul_2exp(R3, Bp, 1); mpz_sub(R1, R1, R3);          /* t */
    if (!mpz_divisible_p(W2, R1)) return;
    mpz_divexact(W2, W2, R1); mpz_add_ui(W2, W2, 1);                              /* q */
    if (mpz_cmp(W2, W1) > 0) report_mpz(x, W1, W2, eps);
}

static long why[8];
static void defer(u64 x, int reason) { printf("F %s %llu\n", prefix_str, (unsigned long long) x); ndef++; why[reason]++; }

/* ---------------------------------------------------------------- the two-entry problem for one x */
static void solve(u64 x, int eps) {
    mpz_mul_ui(Ap, A, x); mpz_mul_ui(Bp, B, x - 1);
    mpz_mul_2exp(c, Bp, 1); mpz_sub(c, c, Ap);
    if (mpz_sgn(c) <= 0) { nempty++; return; }
    mpz_mul(N, Ap, Bp); mpz_mul_2exp(N, N, 1);
    if (eps > 0) mpz_add(N, N, c); else mpz_sub(N, N, c);
    mpz_sqrt(sN, N);
    mpz_mul_ui(tmin, c, x + 2); mpz_submul_ui(tmin, Bp, 2);
    if (mpz_cmp_ui(tmin, 1) < 0) mpz_set_ui(tmin, 1);
    if (mpz_cmp(tmin, sN) > 0) { nempty++; return; }

    /* p_lo = ceil((tmin + 2B')/c), p_hi = floor((sN + 2B')/c) */
    mpz_t plo, phi, twoB;
    mpz_inits(plo, phi, twoB, NULL);
    mpz_mul_2exp(twoB, Bp, 1);
    mpz_add(tmp, tmin, twoB); mpz_cdiv_q(plo, tmp, c);
    mpz_add(tmp, sN, twoB); mpz_fdiv_q(phi, tmp, c);
    if (mpz_cmp(plo, phi) > 0) { nempty++; mpz_clears(plo, phi, twoB, NULL); return; }

    /* split point p_d: trial division for p in [p_lo, p_d), sums for p in [p_d, p_hi] */
    double Nd = mpz_get_d(N), cd = mpz_get_d(c), sNd = mpz_get_d(sN), tmd = mpz_get_d(tmin), Bd = mpz_get_d(twoB);
    double w = three_all ? 6.0 : 2.0;
    double ts = sqrt(Nd / (1.0 + A1 * cd * w / A2));
    if (FORCE == 1) ts = sNd + 1; else if (FORCE == 2) ts = tmd;
    if (ts < tmd) ts = tmd;
    if (ts > sNd + 1) ts = sNd + 1;
    double est = A1 * (ts - tmd) / cd + A2 * ((ts + Nd / ts - 2 * sNd) / cd) / (cd * w);
    if (est > FCOST) { defer(x, 1); mpz_clears(plo, phi, twoB, NULL); return; }
    double pdd = ceil((ts + Bd) / cd);
    mpz_t pd; mpz_init(pd);
    if (pdd > 1.8e19) mpz_add_ui(pd, phi, 1); else mpz_set_d(pd, pdd);
    if (mpz_cmp(pd, plo) < 0) mpz_set(pd, plo);
    mpz_add_ui(tmp, phi, 1); if (mpz_cmp(pd, tmp) > 0) mpz_set(pd, tmp);

    /* size guards: the fast paths keep A'p and c p below 2^125; otherwise the wide paths are used, in which the trial
       division tests whether t divides N (equivalent, since gcd(t, c) = 1) with t < 2^64, and the sums use GMP */
    if (!fits(pd, 62)) { defer(x, 2); mpz_clears(plo, phi, twoB, pd, NULL); return; }
    int wide = FORCE == 3;
    mpz_mul(tmp, Ap, pd); if (!fits(tmp, 125)) wide = 1;
    mpz_mul(tmp, c, pd); if (!fits(tmp, 125)) wide = 1;
    if (wide) {
        /* t = c p - 2B' < 2^64 for p < p_d: p_d <= floor((2^64 - 1 + 2B')/c) + 1 */
        mpz_set_ui(tmp, 1); mpz_mul_2exp(tmp, tmp, 64); mpz_sub_ui(tmp, tmp, 1); mpz_add(tmp, tmp, twoB);
        mpz_fdiv_q(tmp, tmp, c); mpz_add_ui(tmp, tmp, 1);
        if (mpz_cmp(pd, tmp) > 0) mpz_set(pd, tmp);
        if (mpz_cmp(pd, plo) < 0) mpz_set(pd, plo);
    }

    /* ---- trial division, wide: N mod t by limbs, t < 2^64 */
    if (wide && mpz_cmp(plo, pd) < 0) {
        u64 P0 = mpz_get_ui(plo), P1 = mpz_get_ui(pd);
        u64 NL[16]; size_t nl = 0;
        if (mpz_sizeinbase(N, 2) > 16 * 64) { defer(x, 5); mpz_clears(plo, phi, twoB, pd, NULL); return; }
        mpz_export(NL, &nl, -1, 8, 0, 0, N);
        mpz_mul(tmp, c, plo); mpz_sub(tmp, tmp, twoB);           /* t at p_lo, below 2^64 */
        u64 tlo = mpz_get_ui(tmp);
        if (!fits(c, 64)) {                                       /* then p_lo is the only value with t < 2^64 */
            ntd += 1;
            u64 r = 0;
            for (long i = (long) nl - 1; i >= 0; i--) {
                u64 qq, rr; __asm__("divq %4" : "=a"(qq), "=d"(rr) : "a"(NL[i]), "d"(r), "rm"(tlo)); (void) qq; r = rr;
            }
            if (r == 0) trial_hit_wide(x, P0, eps);
        } else {
            u64 c64 = mpz_get_ui(c);
            int idx[NWH], inc[NWH];
            for (int i = 0; i < nwh; i++) { int l = WHMOD[whm[i]]; idx[i] = (int) (P0 % l); inc[i] = 64 % l; }
            for (u64 b0 = P0; b0 < P1; b0 += 64) {
                u64 mask = ~0ULL;
                for (int i = 0; i < nwh; i++) {
                    int l = WHMOD[whm[i]];
                    mask &= WW[whm[i]][idx[i]];
                    idx[i] += inc[i]; if (idx[i] >= l) idx[i] -= l;
                }
                if (P1 - b0 < 64) mask &= (1ULL << (P1 - b0)) - 1;
                while (mask) {
                    int b = __builtin_ctzll(mask); mask &= mask - 1;
                    u64 P = b0 + b;
                    u64 t = tlo + c64 * (P - P0);
                    ntd += 1;
                    u64 r = 0;
                    for (long i = (long) nl - 1; i >= 0; i--) {
                        u64 qq, rr; __asm__("divq %4" : "=a"(qq), "=d"(rr) : "a"(NL[i]), "d"(r), "rm"(t)); (void) qq; r = rr;
                    }
                    if (r == 0) trial_hit_wide(x, P, eps);
                }
            }
        }
    }

    /* ---- trial division */
    if (!wide && mpz_cmp(plo, pd) < 0) {
        u64 P0 = mpz_get_ui(plo), P1 = mpz_get_ui(pd);
        u128 Ap128 = mpz_get_u128(Ap), c128 = mpz_get_u128(c);
        mpz_mul(tmp, c, plo); mpz_sub(tmp, tmp, twoB);           /* t at p_lo */
        u128 tlo = mpz_get_u128(tmp);
        int idx[NWH], inc[NWH];
        for (int i = 0; i < nwh; i++) { int l = WHMOD[whm[i]]; idx[i] = (int) (P0 % l); inc[i] = 64 % l; }
        for (u64 b0 = P0; b0 < P1; b0 += 64) {
            u64 mask = ~0ULL;
            for (int i = 0; i < nwh; i++) {
                int l = WHMOD[whm[i]];
                mask &= WW[whm[i]][idx[i]];
                idx[i] += inc[i]; if (idx[i] >= l) idx[i] -= l;
            }
            if (P1 - b0 < 64) mask &= (1ULL << (P1 - b0)) - 1;
            while (mask) {
                int b = __builtin_ctzll(mask); mask &= mask - 1;
                u64 P = b0 + b;
                u128 t = tlo + c128 * (P - P0);
                u128 X = Ap128 * P;
                if (eps > 0) X += 1; else X -= 1;
                ntd += 1;
                if (mod128_by(X, t) == 0) {
                    u128 q = 1 + X / t;
                    if (q > P) report(x, P, q, eps);
                }
            }
        }
    }

    /* ---- sums */
    if (mpz_cmp(pd, phi) <= 0) {
        /* t_d = c p_d - 2B'; sigma_hi = floor((t_d + floor(N/t_d) + 4B')/c); sigma_lo = ceil((2 sN + 4B')/c) */
        mpz_t shi, slo; mpz_inits(shi, slo, NULL);
        mpz_mul(td, c, pd); mpz_sub(td, td, twoB);
        mpz_fdiv_q(tmp, N, td); mpz_add(tmp, tmp, td); mpz_addmul_ui(tmp, twoB, 2); mpz_fdiv_q(shi, tmp, c);
        mpz_mul_2exp(tmp, sN, 1); mpz_addmul_ui(tmp, twoB, 2); mpz_cdiv_q(slo, tmp, c);
        /* class: sigma = (2B' - eps) (2B')^(-1) mod c */
        mpz_mod(tmp, twoB, c);
        if (!mpz_invert(inv, tmp, c)) {
            if (mpz_cmp_ui(c, 1) == 0) mpz_set_ui(inv, 0);
            else { defer(x, 3); mpz_clears(plo, phi, twoB, pd, shi, slo, NULL); return; }
        }
        if (eps > 0) mpz_sub_ui(tmp, twoB, 1); else mpz_add_ui(tmp, twoB, 1);
        mpz_mul(cls, tmp, inv); mpz_mod(cls, cls, c);
        /* first sigma >= slo in the class, then the conditions modulo 2 and 3 */
        mpz_sub(tmp, cls, slo); mpz_mod(tmp, tmp, c); mpz_add(sig, slo, tmp);
        int wq = three_all ? 6 : 2, found = 0;
        for (int i = 0; i < wq; i++) {
            if (mpz_even_p(sig) && (!three_all || mpz_fdiv_ui(sig, 3) == 1)) { found = 1; break; }
            mpz_add(sig, sig, c);
        }
        unsigned long gw = mpz_gcd_ui(NULL, c, wq), mult = wq / gw;   /* step h = lcm(c, wq) = c * mult */
        if (found && mpz_cmp(sig, shi) <= 0 && (FORCE == 3 || !fits(shi, 62))) {
            /* ---- sums, wide: sigma and pi as GMP integers; the filters work on residues */
            static mpz_t hh, gg, ss, pp, DD, ee, P2, Q2, pi0z; static int init = 0;
            if (!init) { mpz_inits(hh, gg, ss, pp, DD, ee, P2, Q2, pi0z, NULL); init = 1; }
            mpz_mul(pi0z, twoB, sig); mpz_sub(pi0z, pi0z, twoB); if (eps > 0) mpz_add_ui(pi0z, pi0z, 1); else mpz_sub_ui(pi0z, pi0z, 1);
            if (!mpz_divisible_p(pi0z, c)) { fprintf(stderr, "scan3: class error\n"); exit(4); }
            mpz_divexact(pi0z, pi0z, c);
            mpz_mul_ui(hh, c, mult); mpz_mul_ui(gg, twoB, mult);
            mpz_sub(tmp, shi, sig); mpz_fdiv_q(tmp, tmp, hh);
            if (!fits(tmp, 62)) { defer(x, 4); mpz_clears(plo, phi, twoB, pd, shi, slo, NULL); return; }
            u64 nk = mpz_get_ui(tmp) + 1;
            nsig += (double) nk;
#define WIDE_TEST(k) do { \
                mpz_set(ss, sig); mpz_addmul_ui(ss, hh, (k)); mpz_set(pp, pi0z); mpz_addmul_ui(pp, gg, (k)); \
                mpz_mul(DD, ss, ss); mpz_submul_ui(DD, pp, 4); \
                if (mpz_sgn(DD) > 0) { nsurv++; if (mpz_perfect_square_p(DD)) { \
                    mpz_sqrt(ee, DD); mpz_sub(P2, ss, ee); mpz_fdiv_q_2exp(P2, P2, 1); mpz_add(Q2, ss, ee); mpz_fdiv_q_2exp(Q2, Q2, 1); \
                    report_mpz(x, P2, Q2, eps); } } } while (0)
            int use[NSUM];
            if (sum_moduli((double) nk, 150.0, use) == 0) {
                for (u64 k = 0; k < nk; k++) WIDE_TEST(k);
            } else {
                for (int m = 0; m < NSUM; m++) {
                    int l = SUMMOD[m];
                    if (!use[m]) continue;
                    u64 sm = mpz_fdiv_ui(sig, l), hm = mpz_fdiv_ui(hh, l), pm = mpz_fdiv_ui(pi0z, l), gm = mpz_fdiv_ui(gg, l);
                    sum_windows(m, sm, hm, pm, gm);
                }
                int idx[NSUM], inc[NSUM];
                for (int m = 0; m < NSUM; m++) { idx[m] = 0; inc[m] = 64 % SUMMOD[m]; }
                for (u64 k0 = 0; k0 < nk; k0 += 64) {
                    u64 mask = ~0ULL;
                    for (int m = 0; m < NSUM; m++) {
                        mask &= SW[m][idx[m]];
                        idx[m] += inc[m]; if (idx[m] >= SUMMOD[m]) idx[m] -= SUMMOD[m];
                    }
                    if (nk - k0 < 64) mask &= (1ULL << (nk - k0)) - 1;
                    while (mask) {
                        int b = __builtin_ctzll(mask); mask &= mask - 1;
                        WIDE_TEST(k0 + b);
                    }
                }
            }
#undef WIDE_TEST
        } else if (found && mpz_cmp(sig, shi) <= 0) {
            u128 s0 = mpz_get_u128(sig), s1 = mpz_get_u128(shi);
            /* pi_0 = (2B' sigma_0 - 2B' + eps)/c, g = 2B' mult, h = c mult */
            mpz_mul(tmp, twoB, sig); mpz_sub(tmp, tmp, twoB); if (eps > 0) mpz_add_ui(tmp, tmp, 1); else mpz_sub_ui(tmp, tmp, 1);
            if (!mpz_divisible_p(tmp, c)) { fprintf(stderr, "scan3: class error\n"); exit(4); }
            mpz_divexact(tmp, tmp, c);
            u128 pi0 = mpz_get_u128(tmp);
            mpz_mul_ui(tmp, c, mult); int hfits = fits(tmp, 63); u128 h = hfits ? mpz_get_u128(tmp) : 0;
            mpz_mul_ui(tmp, twoB, mult); u128 g = mpz_get_u128(tmp);    /* < 2^75 */
            u64 nk = hfits ? (u64) ((s1 - s0) / h) + 1 : 1;
            nsig += (double) nk;
            int use[NSUM];
            if (sum_moduli((double) nk, 25.0, use) == 0) {
                u128 s = s0, pi = pi0;
                for (u64 k = 0; k < nk; k++, s += h, pi += g) {
                    i128 D = (i128) (s * s) - (i128) (4 * pi);
                    if (D <= 0) continue;
                    nsurv++;
                    u128 e = isqrt128((u128) D);
                    if (e * e == (u128) D) report(x, (s - e) / 2, (s + e) / 2, eps);
                }
            } else {
                for (int m = 0; m < NSUM; m++) {
                    int l = SUMMOD[m];
                    if (!use[m]) continue;
                    u64 sm = mod128(s0, l), hm = mod128(h, l), pm = mod128(pi0, l), gm = mod128(g, l);
                    sum_windows(m, sm, hm, pm, gm);
                }
                int idx[NSUM], inc[NSUM];
                for (int m = 0; m < NSUM; m++) { idx[m] = 0; inc[m] = 64 % SUMMOD[m]; }
                for (u64 k0 = 0; k0 < nk; k0 += 64) {
                    u64 mask = ~0ULL;
                    for (int m = 0; m < NSUM; m++) {
                        mask &= SW[m][idx[m]];
                        idx[m] += inc[m]; if (idx[m] >= SUMMOD[m]) idx[m] -= SUMMOD[m];
                    }
                    if (nk - k0 < 64) mask &= (1ULL << (nk - k0)) - 1;
                    while (mask) {
                        int b = __builtin_ctzll(mask); mask &= mask - 1;
                        u64 k = k0 + b;
                        u128 s = s0 + (u128) k * h, pi = pi0 + (u128) k * g;
                        i128 D = (i128) (s * s) - (i128) (4 * pi);
                        nsurv++;
                        if (D <= 0) continue;
                        u128 e = isqrt128((u128) D);
                        if (e * e == (u128) D) report(x, (s - e) / 2, (s + e) / 2, eps);
                    }
                }
            }
        }
        mpz_clears(shi, slo, NULL);
    }
    mpz_clears(plo, phi, twoB, pd, NULL);
}

/* ---------------------------------------------------------------- the interval for x */
static u64 *bp = NULL; static long nbp = 0; static u64 bplim = 0;
static void base_primes(u64 lim) {
    if (lim <= bplim) return;
    char *s = calloc(lim + 1, 1); nbp = 0;
    bp = realloc(bp, sizeof(u64) * (lim / 2 + 10));
    for (u64 i = 2; i <= lim; i++) {
        if (!s[i]) { bp[nbp++] = i; if (i * i <= lim) for (u64 k = i * i; k <= lim; k += i) s[k] = 1; }
    }
    free(s); bplim = lim;
}
static u64 isqrt64(u64 n) { u64 r = (u64) sqrtl((long double) n); while (r * r > n) r--; while ((r + 1) * (r + 1) <= n) r++; return r; }

int main(int argc, char **argv) {
    if (argc > 1) A1 = atof(argv[1]);
    if (argc > 2) A2 = atof(argv[2]);
    if (argc > 3) FCOST = atof(argv[3]);
    if (argc > 4) FORCE = atoi(argv[4]);
    mpz_inits(A, B, Ap, Bp, c, N, sN, tmin, tmp, tmp2, pz, qz, td, sig, cls, inv, R1, R2, R3, W1, W2, NULL);
    static char line[1 << 16];
    while (fgets(line, sizeof line, stdin)) {
        char *ptr = line; int eps, mode, j; int off;
        if (sscanf(ptr, "%d %d %d%n", &eps, &mode, &j, &off) < 3) continue;
        ptr += off;
        u64 *xs = malloc(sizeof(u64) * (j + 1));
        mpz_set_ui(A, 1); mpz_set_ui(B, 1);
        int ps = 0; prefix_str[0] = 0;
        for (int i = 0; i < j; i++) {
            unsigned long long v; sscanf(ptr, "%llu%n", &v, &off); ptr += off; xs[i] = v;
            mpz_mul_ui(A, A, v); mpz_mul_ui(B, B, v - 1);
            ps += sprintf(prefix_str + ps, i ? " %llu" : "%llu", v);
        }
        unsigned long long lo, hi; sscanf(ptr, "%llu %llu%n", &lo, &hi, &off); ptr += off;
        int n0 = 0, n1 = 0; u64 R0[256], R1[256];
        if (mode >= 1) {
            sscanf(ptr, "%d%n", &n0, &off); ptr += off;
            for (int i = 0; i < n0; i++) { unsigned long long v; sscanf(ptr, "%llu%n", &v, &off); ptr += off; R0[i] = v; }
            sscanf(ptr, "%d%n", &n1, &off); ptr += off;
            for (int i = 0; i < n1; i++) { unsigned long long v; sscanf(ptr, "%llu%n", &v, &off); ptr += off; R1[i] = v; }
        }
        setup_task(mode, j, xs, lo, n0, R0, n1, R1);
        clock_t t0 = clock();
        long nx = 0; nfound = ndef = nsurv = nempty = 0; ntd = nsig = 0;
        if (lo < 3) lo = 3;
        if (mode == 0) {
            base_primes(isqrt64(hi) + 1);
            const u64 SEG = 1 << 20;                     /* odd numbers per segment */
            unsigned char *seg = malloc(SEG);
            u64 start = lo | 1;
            while (start <= hi) {
                u64 end = start + 2 * (SEG - 1); if (end > hi) end = hi;
                u64 cnt = (end - start) / 2 + 1;
                memset(seg, 1, cnt);
                for (long i = 1; i < nbp; i++) {
                    u64 pr = bp[i]; if (pr * pr > end) break;
                    u64 f = (start + pr - 1) / pr * pr; if (f < pr * pr) f = pr * pr;
                    if ((f & 1) == 0) f += pr;
                    for (u64 m = f; m <= end; m += 2 * pr) seg[(m - start) / 2] = 0;
                }
                for (u64 i = 0; i < cnt; i++) if (seg[i]) {
                    u64 xv = start + 2 * i; if (xv < 3) continue;
                    int adm = 1;
                    for (int t = 0; t < j; t++) if (xv % xs[t] == 1 || xv == xs[t]) { adm = 0; break; }
                    if (!adm) continue;
                    nx++; solve(xv, eps);
                }
                start = end + 2;
            }
            free(seg);
        } else {
            for (u64 xv = lo | 1; xv <= hi; xv += 2) {
                if (mode == 1 && xv % 3 == 0) continue;
                int adm = 1;
                for (int t = 0; t < n0 && adm; t++) if (xv % R0[t] == 0) adm = 0;
                for (int t = 0; t < n1 && adm; t++) if (xv % R1[t] == 1) adm = 0;
                if (!adm) continue;
                nx++; solve(xv, eps);
            }
        }
        printf("T %ld %ld %.0f %.0f %ld %ld %ld %.3f\n", nx, nempty, ntd, nsig, nsurv, nfound, ndef,
               (double) (clock() - t0) / CLOCKS_PER_SEC);
        if (getenv("SCAN3_WHY")) fprintf(stderr, "why %ld %ld %ld %ld %ld %ld\n", why[1], why[2], why[3], why[4], why[5], why[6]);
        fflush(stdout);
        free(xs);
    }
    return 0;
}
