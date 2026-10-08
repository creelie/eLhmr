/*
 tail3.c -- the last three entries of  b (x_1 ... x_k + eps) = a (x_1 - 1) ... (x_k - 1)  for a whole interval of the
 third-to-last entry t = x_{k-2}, by the sum route of Section 4.4 of the paper.  With A'' = A t, B'' = B (t - 1) and
 C'' = a B'' - b A'', the last two entries p < q satisfy  C'' pq = a B'' (p + q - 1) + b eps,  so sigma = p + q - 1 lies
 in one residue class modulo C'' / gcd(a B'', C'').

 Input lines:  a b eps j x_1 ... x_j tlo thi mode  [n0 r0_1 .. r0_n0 n1 r1_1 .. r1_n1]
   mode 0: t runs over the primes in [tlo, thi] with t > x_j and t != 1 mod x_i.
   mode 1: as mode 0, but the long problems are only counted (histogram of log10(C''^3 / N)).
   mode 2: t runs over the ODD INTEGERS in [tlo, thi], t > x_j, with t != 1 mod x_i, t != 0 mod r0_i (the odd primes
           of B = prod(x_i - 1), plus 3 in the search prime to 3) and t != 1 mod r1_i (the primes of A = prod x_i).
           These are the conditions gcd(t, x_i - 1) = gcd(x_i, t - 1) = 1, which every integer solution satisfies.
   mode 3: as mode 2, and completions in which 3 divides p or q are printed as 'D' lines instead of 'S' lines.
 Output per task:  "T <nt> <nsingle> <nsurv> <nmulti> <work> <nfound> <sec> <ndeferred> <nD>", one line
 "S x_1 .. x_j t p q" per integer completion (p, q not necessarily prime; the caller checks primality where it
 matters), and one line "F x_1 .. x_j t" per deferred problem, where the sum route would need more than 2e7 steps;
 the caller solves those by a complete factorisation of N = b (a A'' B'' + eps C'').

 Exactness: the window [S_lo, S_hi] for sigma is computed in long double and widened by a relative margin 1e-9 plus
 4; only the class representative(s) inside the widened window are tested, and each test is exact (mpz):
 P = (aB'' sigma + b eps)/C'' must be an integer, (sigma+1)^2 - 4P a perfect square, p > t, q > p.  A true
 completion has sigma in the exact window, hence in the widened one, so no completion is missed.

 Build:  gcc -O2 -o tail3 tail3.c -lgmp -lm
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <gmp.h>

typedef unsigned long long u64;

static u64 *bp = NULL; static long nbp = 0; static u64 bplim = 0;
static void base_primes(u64 lim) {
    if (lim <= bplim) return;
    char *s = calloc(lim + 1, 1); nbp = 0;
    bp = realloc(bp, sizeof(u64) * (lim / 2 + 10));
    for (u64 i = 2; i <= lim; i++) {
        if (!s[i]) { bp[nbp++] = i; if (i * i <= lim) for (u64 j = i * i; j <= lim; j += i) s[j] = 1; }
    }
    free(s); bplim = lim;
}
static u64 isqrt64(u64 n) { u64 r = (u64) sqrtl((long double) n); while (r * r > n) r--; while ((r + 1) * (r + 1) <= n) r++; return r; }

static double hist[64];

int main(int argc, char **argv) {
    char line[1 << 16];
    mpz_t A1, B1, A2, B2, aB2, d, N, tmp, inv, sig, P, S, D, rt, e, f, q1, r1, emin, ed, sN, g, m, sig0;
    mpz_inits(A1, B1, A2, B2, aB2, d, N, tmp, inv, sig, P, S, D, rt, e, f, q1, r1, emin, ed, sN, g, m, sig0, NULL);
    while (fgets(line, sizeof line, stdin)) {
        char *ptr = line; int a, b, eps, j, mode; long off;
        if (sscanf(ptr, "%d %d %d %d%ln", &a, &b, &eps, &j, &off) < 4) continue; ptr += off;
        u64 *ch = malloc(sizeof(u64) * (j + 1));
        for (int i = 0; i < j; i++) { sscanf(ptr, "%llu%ln", &ch[i], &off); ptr += off; }
        u64 tlo, thi; sscanf(ptr, "%llu %llu %d%ln", &tlo, &thi, &mode, &off); ptr += off;
        int n0 = 0, n1 = 0; u64 *R0 = NULL, *R1 = NULL;
        if (mode >= 2) {
            sscanf(ptr, "%d%ln", &n0, &off); ptr += off; R0 = malloc(sizeof(u64) * (n0 + 1));
            for (int i = 0; i < n0; i++) { sscanf(ptr, "%llu%ln", &R0[i], &off); ptr += off; }
            sscanf(ptr, "%d%ln", &n1, &off); ptr += off; R1 = malloc(sizeof(u64) * (n1 + 1));
            for (int i = 0; i < n1; i++) { sscanf(ptr, "%llu%ln", &R1[i], &off); ptr += off; }
        }
        mpz_set_ui(A1, 1); mpz_set_ui(B1, 1);
        for (int i = 0; i < j; i++) { mpz_mul_ui(A1, A1, ch[i]); mpz_mul_ui(B1, B1, ch[i] - 1); }
        u64 pmax = j ? ch[j - 1] : 1;
        if (tlo <= pmax) tlo = pmax + 1;
        if (tlo < 3) tlo = 3;
        clock_t c0 = clock();
        long nt = 0, nsingle = 0, nsurv = 0, nmulti = 0, nfound = 0, ndef = 0, ndisc = 0; double work = 0;
        if (mode < 2) base_primes(isqrt64(thi) + 1);
        const u64 SEG = 1ULL << 22;           /* odd numbers per segment */
        unsigned char *seg = malloc(SEG);
        u64 lo = tlo | 1ULL;
        while (lo <= thi) {
            u64 cnt = SEG; if (lo + 2 * (cnt - 1) > thi) cnt = (thi - lo) / 2 + 1;
            u64 hi = lo + 2 * (cnt - 1);
            memset(seg, 1, cnt);
            if (mode < 2) for (long i = 1; i < nbp; i++) {           /* odd base primes (prime modes only) */
                u64 p = bp[i]; if (p * p > hi) break;
                u64 st = p * p; if (st < lo) { st = ((lo + p - 1) / p) * p; if (!(st & 1)) st += p; }
                for (u64 x = st; x <= hi; x += 2 * p) seg[(x - lo) >> 1] = 0;
            }
            for (int i = 0; i < j; i++) {              /* t = 1 mod p_i excluded (odd t: t = 1 mod 2p_i) */
                u64 p = ch[i]; if (p == 2) continue;
                u64 st; u64 mod2p = 2 * p; u64 r = (lo - 1) % mod2p; st = r ? lo + (mod2p - r) : lo;
                for (u64 x = st; x <= hi; x += mod2p) seg[(x - lo) >> 1] = 0;
            }
            if (mode >= 2) {
                for (int i = 0; i < n0; i++) {         /* t = 0 mod r excluded: odd t = r mod 2r */
                    u64 r = R0[i]; if (r < 3) continue; u64 m2 = 2 * r;
                    u64 st = lo + ((r + m2 - lo % m2) % m2);
                    for (u64 x = st; x <= hi; x += m2) seg[(x - lo) >> 1] = 0;
                }
                for (int i = 0; i < n1; i++) {         /* t = 1 mod r excluded: odd t = 1 mod 2r */
                    u64 r = R1[i]; if (r < 3) continue; u64 m2 = 2 * r;
                    u64 rr = (lo - 1) % m2; u64 st = rr ? lo + (m2 - rr) : lo;
                    for (u64 x = st; x <= hi; x += m2) seg[(x - lo) >> 1] = 0;
                }
            }
            for (u64 idx = 0; idx < cnt; idx++) {
                if (!seg[idx]) continue;
                u64 t = lo + 2 * idx;
                if (t < 3) continue;
                /* t prime (sieved; t <= sqrt bound handled: base primes themselves) */
                nt++;
                mpz_mul_ui(A2, A1, t); mpz_mul_ui(B2, B1, t - 1);
                mpz_mul_ui(aB2, B2, a);
                mpz_mul_ui(tmp, A2, b); mpz_sub(d, aB2, tmp);
                if (mpz_sgn(d) <= 0) continue;
                /* approximate window for S = p + q  (sigma = S - 1) */
                long double ld = mpz_get_d(d), lA = mpz_get_d(A2), lB = mpz_get_d(B2);
                long double laB = (long double) a * lB;
                long double lN = (long double) b * ((long double) a * lA * lB + (long double) eps * ld);
                long double lsN = sqrtl(lN);
                long double lemin = ld * (long double) (t + 1) - laB;     /* may be inaccurate: guard below */
                long double Shi, Slo = (2 * lsN + 2 * laB) / ld;
                mpz_gcd(g, aB2, d);
                int multi = 0;
                if (mpz_cmp_ui(g, 1) != 0) multi = 1;
                if (!multi) {
                    /* exact e_min when cancellation is possible */
                    mpz_mul_ui(emin, d, t + 1); mpz_sub(emin, emin, aB2);
                    if (mpz_sgn(emin) <= 0) multi = 1;
                    else {
                        lemin = mpz_get_d(emin);
                        if (lemin > lsN * (1 + 1e-12L) + 2) continue;   /* no e in [e_min, sqrt N] */
                        Shi = (lemin + lN / lemin + 2 * laB) / ld;
                        if ((Shi - Slo) > 0.25L * ld) multi = 1;
                    }
                }
                if (!multi) {
                    nsingle++;
                    mpz_mod(tmp, aB2, d);
                    if (!mpz_invert(inv, tmp, d)) { multi = 1; }
                    else {
                        mpz_mul_si(sig0, inv, -(long) b * eps); mpz_mod(sig0, sig0, d);
                        long double s0 = mpz_get_d(sig0);
                        long double wlo = (Slo - 1) - 1e-9L * (Shi + 1) - 4, whi = (Shi - 1) + 1e-9L * (Shi + 1) + 4;
                        /* candidates sig = sig0 + k d, k integer, inside [wlo, whi] */
                        long double k0 = ceill((wlo - s0) / ld), k1 = floorl((whi - s0) / ld);
                        if (fabsl(k0) > 1e17L || fabsl(k1) > 1e17L || k1 - k0 > 8) goto multipath;
                        for (long double kk = k0; kk <= k1; kk += 1) {
                            nsurv++;
                            long long ki = (long long) kk;
                            mpz_set_si(tmp, ki); mpz_mul(sig, tmp, d); mpz_add(sig, sig, sig0);
                            if (mpz_sgn(sig) < 0) continue;
                            mpz_mul(P, aB2, sig); mpz_add_ui(P, P, 0);
                            if (b * eps >= 0) mpz_add_ui(P, P, b * eps); else mpz_sub_ui(P, P, -b * eps);
                            if (!mpz_divisible_p(P, d)) continue;
                            mpz_divexact(P, P, d);
                            mpz_add_ui(S, sig, 1); mpz_mul(D, S, S); mpz_submul_ui(D, P, 4);
                            if (mpz_sgn(D) < 0 || !mpz_perfect_square_p(D)) continue;
                            mpz_sqrt(rt, D); mpz_sub(e, S, rt);
                            if (mpz_odd_p(e)) continue;
                            mpz_tdiv_q_2exp(e, e, 1); mpz_add(f, S, rt); mpz_tdiv_q_2exp(f, f, 1);
                            if (mpz_cmp_ui(e, t) <= 0 || mpz_cmp(f, e) <= 0) continue;
                            if (mode == 3 && (mpz_divisible_ui_p(e, 3) || mpz_divisible_ui_p(f, 3))) { ndisc++; printf("D"); }
                            else { nfound++; printf("S"); }
                            for (int i = 0; i < j; i++) printf(" %llu", ch[i]);
                            gmp_printf(" %llu %Zd %Zd\n", t, e, f);
                        }
                        continue;
                    }
                }
                multipath:
                /* multi: exact balanced sum route */
                nmulti++;
                mpz_mul(N, A2, B2); mpz_mul_ui(N, N, a);
                if (eps > 0) mpz_add(N, N, d); else mpz_sub(N, N, d);
                mpz_mul_ui(N, N, b);
                {   double th = 3 * log10(mpz_get_d(d)) - log10(mpz_get_d(N));
                    int hb = (int) floor(th) + 40; if (hb < 0) hb = 0; if (hb > 63) hb = 63; hist[hb] += 1; }
                if (mode == 1) continue;
                {   /* deferred: the balanced route would need more than 2e7 steps -> print the problem (mode 0) */
                    double est = 2 * sqrt(mpz_get_d(N) / pow(mpz_get_d(d), 3));
                    if (est > 2e7) { printf("F"); for (int i = 0; i < j; i++) printf(" %llu", ch[i]); printf(" %llu\n", t); ndef++; continue; }
                }
                mpz_sqrt(sN, N);
                mpz_mul_ui(emin, d, t + 1); mpz_sub(emin, emin, aB2);
                if (mpz_sgn(emin) < 1) mpz_set_ui(emin, 1);
                if (mpz_cmp(emin, sN) > 0) continue;
                mpz_tdiv_q(tmp, N, d); mpz_sqrt(ed, tmp); if (mpz_cmp(ed, emin) < 0) mpz_set(ed, emin);
                if (mpz_cmp(ed, sN) > 0) { mpz_add_ui(ed, sN, 1); }
                /* trial division: e = -aB2 mod d, e in [emin, ed) */
                mpz_neg(r1, aB2); mpz_mod(r1, r1, d);
                mpz_sub(tmp, r1, emin); mpz_mod(tmp, tmp, d); mpz_add(e, emin, tmp);
                while (mpz_cmp(e, ed) < 0) {
                    work += 1;
                    if (mpz_divisible_p(N, e)) {
                        mpz_divexact(f, N, e);
                        mpz_add(tmp, e, aB2); mpz_add(q1, f, aB2);
                        if (mpz_divisible_p(tmp, d) && mpz_divisible_p(q1, d)) {
                            mpz_divexact(tmp, tmp, d); mpz_divexact(q1, q1, d);
                            if (mpz_cmp_ui(tmp, t) > 0 && mpz_cmp(q1, tmp) > 0) {
                                if (mode == 3 && (mpz_divisible_ui_p(tmp, 3) || mpz_divisible_ui_p(q1, 3))) { ndisc++; printf("D"); }
                                else { nfound++; printf("S"); }
                                for (int i = 0; i < j; i++) printf(" %llu", ch[i]);
                                gmp_printf(" %llu %Zd %Zd\n", t, tmp, q1);
                            }
                        }
                    }
                    mpz_add(e, e, d);
                }
                if (mpz_cmp(ed, sN) <= 0) {
                    /* sums: sigma = sig0 mod m, m = d/g, g | b eps required */
                    if (mpz_cmp_ui(g, (unsigned long) labs((long) b * eps)) > 0) continue;
                    long gg = mpz_get_ui(g);
                    if ((b * eps) % gg != 0) continue;
                    mpz_divexact(m, d, g);
                    mpz_divexact(tmp, aB2, g); mpz_mod(tmp, tmp, m);
                    if (mpz_cmp_ui(m, 1) == 0) mpz_set_ui(sig0, 0);
                    else { mpz_invert(inv, tmp, m); mpz_mul_si(sig0, inv, -(long) b * eps / gg); mpz_mod(sig0, sig0, m); }
                    /* S_hi = (ed + N/ed + 2aB2)/d ; S_lo = ceil((2 sN + 2aB2)/d) - 2 */
                    mpz_tdiv_q(tmp, N, ed); mpz_add(tmp, tmp, ed); mpz_addmul_ui(tmp, aB2, 2); mpz_fdiv_q(q1, tmp, d); /* S_hi */
                    mpz_mul_ui(tmp, sN, 2); mpz_addmul_ui(tmp, aB2, 2); mpz_cdiv_q(r1, tmp, d); mpz_sub_ui(r1, r1, 2);
                    if (mpz_sgn(r1) < 0) mpz_set_ui(r1, 0);
                    /* sig = first >= r1 - 1 in class */
                    mpz_sub_ui(r1, r1, 1);
                    mpz_sub(tmp, sig0, r1); mpz_mod(tmp, tmp, m); mpz_add(sig, r1, tmp);
                    while (1) {
                        mpz_add_ui(S, sig, 1); if (mpz_cmp(S, q1) > 0) break;
                        work += 1;
                        mpz_mul(P, aB2, sig);
                        if (b * eps >= 0) mpz_add_ui(P, P, b * eps); else mpz_sub_ui(P, P, -b * eps);
                        if (mpz_divisible_p(P, d)) {
                            mpz_divexact(P, P, d);
                            mpz_mul(D, S, S); mpz_submul_ui(D, P, 4);
                            if (mpz_sgn(D) >= 0 && mpz_perfect_square_p(D)) {
                                mpz_sqrt(rt, D); mpz_sub(e, S, rt);
                                if (mpz_even_p(e)) {
                                    mpz_tdiv_q_2exp(e, e, 1); mpz_add(f, S, rt); mpz_tdiv_q_2exp(f, f, 1);
                                    /* require C p - aB >= ed (else counted by trial division) */
                                    mpz_mul(tmp, d, e); mpz_sub(tmp, tmp, aB2);
                                    if (mpz_cmp_ui(e, t) > 0 && mpz_cmp(f, e) > 0 && mpz_cmp(tmp, ed) >= 0) {
                                        if (mode == 3 && (mpz_divisible_ui_p(e, 3) || mpz_divisible_ui_p(f, 3))) { ndisc++; printf("D"); }
                                        else { nfound++; printf("S"); }
                                        for (int i = 0; i < j; i++) printf(" %llu", ch[i]);
                                        gmp_printf(" %llu %Zd %Zd\n", t, e, f);
                                    }
                                }
                            }
                        }
                        mpz_add(sig, sig, m);
                    }
                }
            }
            if (hi >= thi) break;
            lo = hi + 2;
        }
        free(seg); free(ch); free(R0); free(R1);
        double sec = (double) (clock() - c0) / CLOCKS_PER_SEC;
        printf("T %ld %ld %ld %ld %.0f %ld %.4f %ld %ld\n", nt, nsingle, nsurv, nmulti, work, nfound, sec, ndef, ndisc);
        if (mode == 1) { printf("H"); for (int i = 0; i < 64; i++) if (hist[i] > 0) printf(" %d:%.0f", i - 40, hist[i]); printf("\n"); memset(hist, 0, sizeof hist); }
        fflush(stdout);
    }
    return 0;
}
