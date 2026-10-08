\\ Second implementation of the search of Proposition 2.5(i) of the paper, written separately from independent.py.
\\ Decides whether some set of at most K primes >= 5, no one of which divides another minus 1, has
\\ prod p/(p-1) >= V.  Depth-first recursion; every node carries the list of its candidates, the primes above its
\\ last prime that are not 1 modulo any of its primes, and a child's list is the parent's list filtered by the child's prime.  Logarithms are
\\ computed to 57 digits; a bound within 10^-40 of log V is decided in exact rational arithmetic.
\\ Usage: printf 'K = 10000; V = 3 - 10^-30; LIM = 2*10^6\n\\r independent.gp\n' | gp -q
\\ With mod3 = 1 the allowed primes are those congruent to 2 modulo 3.

default(parisize, 4*10^9);
default(realprecision, 57);
if (type(K) != "t_INT", K = 1000);
if (type(V) != "t_FRAC" && type(V) != "t_INT", V = 3 - 10^-30);
if (type(LIM) != "t_INT", LIM = 10^6);
if (type(mod3) != "t_INT", mod3 = 0);

PR = List();
forprime (p = 5, LIM, if (!mod3 || p % 3 == 2, listput(PR, p)));
PR = Vecsmall(Vec(PR));
NP = #PR;
LG = vector(NP, i, log(PR[i] / (PR[i] - 1.)));
LV = log(V * 1.);
EPS = 10^-40;
nodes = 0; maxdepth = 0; found = 0; exact = 0;
bydepth = vector(200);

exactprod(ch) = prod(i = 1, #ch, ch[i] / (ch[i] - 1));

\\ ch: chosen primes (increasing); lp: log of their product; a: indices of the candidates above the last prime
visit(ch, lp, a) = {
  my(m = K - #ch, n = #a, pre, ub, t, cb, q, b);
  nodes++; maxdepth = max(maxdepth, #ch); bydepth[#ch + 1]++;
  if (lp >= LV - EPS, exact++; if (exactprod(ch) >= V, found = ch; return(1)));
  if (m == 0, return(0));
  if (n < m + 1, error("prime table too short"));
  pre = vector(n + 1); pre[1] = 0.;
  for (i = 1, n, pre[i + 1] = pre[i] + LG[a[i]]);
  \\ pre[i+1] is the sum over a[1..i]
  ub = lp + pre[m + 1];
  if (ub < LV - EPS, return(0));
  if (ub < LV + EPS, exact++;
    if (exactprod(concat(ch, vector(m, i, PR[a[i]]))) < V, return(0)));
  t = 1;
  while (1,
    if (t > n - m, error("prime table too short for children"));
    \\ bound for the child a[t]: its factor and the m - 1 candidates that follow it
    cb = lp + LG[a[t]] + pre[t + m] - pre[t + 1];
    if (cb < LV - EPS, break);
    if (cb < LV + EPS,
      exact++;
      if (exactprod(concat(concat(ch, [PR[a[t]]]), vector(m - 1, i, PR[a[t + i]]))) < V, t++; next));
    q = PR[a[t]];
    b = select(x -> PR[x] % q != 1, a[t + 1 .. n]);
    if (visit(concat(ch, [q]), lp + LG[a[t]], b), return(1));
    t++);
  0;
}

{
  my(t0 = getabstime());
  visit([], 0., vector(NP, i, i));
  printf("K = %d, V = %s (%.15f), %s, primes up to %d\n", K, V, V * 1., if (mod3, "p = 2 mod 3", "p >= 5"), LIM);
  if (found, printf("FOUND a set of %d primes: %s\n", #found, found[1 .. min(#found, 20)]),
    printf("none\n"));
  printf("nodes %d, max depth %d, exact checks %d, %.1f s\n", nodes, maxdepth, exact, (getabstime() - t0) / 1000.);
  printf("nodes by depth: %s\n", bydepth[1 .. maxdepth + 1]);
}
quit;
