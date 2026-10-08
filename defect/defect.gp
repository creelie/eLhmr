\\ Second implementation of the searches of Section 9.9 of the paper, written separately from defect_bound.py and
\\ defect_leaves.py.  For a prime l >= 5 and a size K it lists every set S of K primes p >= 5 with p != l,
\\ p != 1 (mod l), no element 1 modulo another, prod_S p/(p-1) < 2, and prod_S p/(p-1) * q/(q-1) > 2 for the least
\\ prime q > max S that is not 1 modulo an element of S.  For each such S it decides n - 1 = 2 phi(n) for n = A q
\\ exactly: C = 2 phi(A) - A, l | C, C | A - 1, and q = (2 phi(A) - 1)/C a prime above max S, not 1 modulo an
\\ element of S.  With stopfirst = 1 it stops at the first set S, which decides whether k = K + 1 is possible.
\\ Depth-first recursion.  A child is created from the candidates of its parent: its bound is the parent's product,
\\ its own prime, the m - 1 candidates of the parent that follow it, and the least allowed q above them.
\\ Candidates are generated with nextprime, so there is no table of primes.  Logarithms to 38 digits; a bound
\\ within 10^-20 of log 2 is decided in exact rational arithmetic.
\\ Usage: echo 'run(7, 58, 0)' | gp -q defect.gp   (sets S of size k - 1 = 57 for l = 7; scan(l, kmax) gives k_l).
\\ The recorded runs: gp -q defect.gp runs.gp < /dev/null

default(debugmem, 0);
default(parisize, 10^9);
default(realprecision, 38);
EPS = 10^-20;
L2 = log(2);

lw(p) = log(p / (p - 1.));
indep(p, S) = for (i = 1, #S, if (p % S[i] == 1, return(0))); 1;
\\ least prime above x not 1 modulo an element of S: the smallest possible largest prime q
finalq(S, x) = my(p = nextprime(x + 1)); while (!indep(p, S), p = nextprime(p + 1)); p;
\\ the first m primes above x that S allows and that avoid l and the class 1 modulo l
cands(S, x, m) = {
  my(v = vector(m), p = x, j = 0);
  while (j < m, p = nextprime(p + 1); if (p != ell && p % ell != 1 && indep(p, S), j++; v[j] = p));
  v;
}
pr(S) = prod(i = 1, #S, S[i] / (S[i] - 1));

leaf(S) = {
  my(q0 = finalq(S, S[#S]), P = pr(S), A, B, C, q);
  if (P >= 2 || P * q0 / (q0 - 1) <= 2, return(0));
  nsets++; lastset = concat(S, [q0]);
  A = prod(i = 1, #S, S[i]); B = prod(i = 1, #S, S[i] - 1); C = 2 * B - A;
  if (C % ell, return(1));
  ndivl++;
  if ((A - 1) % C, return(1));
  ndivA++;
  q = (2 * B - 1) / C;
  if (q > S[#S] && indep(q, S) && isprime(q), listput(sols, concat(S, [q])));
  1;
}

visit(S, lp) = {
  my(m = KK - #S, x = if (#S, S[#S], 3), W, c, pre, t, cb, done, Pc);
  nodes++;
  if (m == 0, return(leaf(S) && stopfirst));
  W = m + 40;
  while (1,
    c = cands(S, x, W);
    pre = vector(W + 1); for (i = 1, W, pre[i + 1] = pre[i] + lw(c[i]));
    done = 0; t = 1;
    while (t + m - 1 <= W,
      cb = lp + pre[t + m] - pre[t] + lw(finalq(S, c[t + m - 1]));
      if (cb < L2 - EPS, done = 1; break);
      if (cb < L2 + EPS && pr(concat(concat(S, c[t .. t + m - 1]), [finalq(S, c[t + m - 1])])) <= 2, done = 1; break);
      t++);
    if (done, break);
    W *= 2);
  \\ children 1 .. t - 1
  for (i = 1, t - 1,
    Pc = lp + lw(c[i]);
    if (Pc >= L2 + EPS, next);
    if (Pc > L2 - EPS && pr(concat(S, [c[i]])) >= 2, next);
    if (visit(concat(S, [c[i]]), Pc), return(1)));
  0;
}

run(l, k, stop) = {
  my(t0 = getabstime());
  ell = l; KK = k - 1; stopfirst = stop;
  nodes = 0; nsets = 0; ndivl = 0; ndivA = 0; sols = List();
  visit([], 0.);
  printf("l = %d, k = %d: sets S %d, with l | C %d, with C | A-1 %d, Lehmer numbers %s (%d nodes, %.1fs)\n",
    l, k, nsets, ndivl, ndivA, Vec(sols), nodes, (getabstime() - t0) / 1000.);
}

\\ least k = K + 1 for which some set S of size K exists, scanning K = 1, 2, ...
scan(l, kmax) = {
  my(t0 = getabstime());
  for (K = 1, kmax - 1,
    ell = l; KK = K; stopfirst = 1; nodes = 0; nsets = 0; ndivl = 0; ndivA = 0; sols = List();
    visit([], 0.);
    if (nsets, printf("l = %d: k_l = %d, witness ends %s (%.1fs)\n", l, K + 1, lastset[#lastset - 3 .. #lastset], (getabstime() - t0) / 1000.); return(K + 1)));
  printf("l = %d: k_l > %d\n", l, kmax);
}
