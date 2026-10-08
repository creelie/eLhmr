\\ factor_class.gp -- the deferred cases of scan3: for each tuple [x_1, ..., x_j, x] in the file IN, with
\\ A' = x_1 ... x_j x, B' = (x_1 - 1) ... (x_j - 1)(x - 1), c = 2B' - A' and N = 2A'B' + EPS c, factor N completely
\\ (factor_proven = 1: every prime factor is proved prime) and list the divisors t of N with t = -2B' (mod c),
\\ c(x + 2) - 2B' <= t and t^2 < N.  Each gives integers p = (t + 2B')/c and q = (N/t + 2B')/c with x < p < q and
\\ A'pq + EPS = 2B'(p - 1)(q - 1).  Output: one line "C x_1 .. x_j x p q isprime(p) isprime(q)" per completion and
\\ a final line "G <tuples> <completions> <largest number of digits of N> <seconds>".
\\ Usage:  echo 'IN="file"; EPS=1;' | cat - factor_class.gp | gp -q -s 200000000
default(factor_proven, 1);
{
my(V = readvec(IN), nc = 0, dmax = 0, t0 = getabstime());
for (i = 1, #V,
  my(w = V[i], j = #w, x = w[j], Ap = prod(k = 1, j, w[k]), Bp = prod(k = 1, j, w[k] - 1), c, N, r, tmin, D);
  c = 2*Bp - Ap; if (c <= 0, next);
  N = 2*Ap*Bp + EPS*c; r = (-2*Bp) % c; tmin = max(1, c*(x + 2) - 2*Bp);
  dmax = max(dmax, #digits(N));
  D = divisors(factor(N));
  for (m = 1, #D,
    my(t = D[m], p, q);
    if (t*t >= N, break);
    if (t < tmin || (t - r) % c, next);
    p = (t + 2*Bp)/c; q = (N/t + 2*Bp)/c;
    if (Ap*p*q + EPS != 2*Bp*(p - 1)*(q - 1) || p <= x || q <= p, error("bad completion ", w));
    nc++;
    print("C ", strjoin(apply(z -> Str(z), w), " "), " ", p, " ", q, " ", isprime(p), " ", isprime(q))));
print("G ", #V, " ", nc, " ", dmax, " ", (getabstime() - t0)/1000.);
}
quit;
