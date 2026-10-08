\\ Second implementation of the search of Proposition 2.5(ii), (iii) of the paper for very large K (primes
\\ q = 2 mod 3), written separately from independent_stream.py.  Decides whether some set of at most K primes q = 2 (mod 3), q >= 5, no one
\\ of which divides another minus 1, has prod q/(q-1) >= V.  Each node of the tree runs once through the primes with
\\ forprime(), keeping only the running count and log-sum of its candidates, the first few of them,
\\ and nothing else.  A node is pruned, or a child rejected, only when its bound is below log V - 10^-20; logarithms
\\ are computed to 38 digits, so rounding cannot reverse a decision.
\\ Usage: printf 'K = 10^7; V = 8/3*(1 - 10^-6); X = 10^9\n\\r independent_stream.gp\n' | gp -q

default(parisize, 10^9);
if (type(K) != "t_INT", K = 10^6);
if (type(V) != "t_FRAC" && type(V) != "t_INT", V = 8/3 * (1 - 10^-6));
if (type(X) != "t_INT", X = 10^9);
LV = log(V * 1.);
EPS = 10^-20;
RMAX = 10^5;
nodes = 0; bydepth = vector(100); result = "none";

\\ one pass for the node S (chosen primes, increasing; last = its last prime, or 2 at the root)
\\ returns 0 if pruned, else the vector of its children
pass(S, last, m, lp) = {
  my(cnt = 0, acc = 0., fq = vector(RMAX), fl = vector(RMAX), fc = vector(RMAX), t, cb, l, ok);
  forprime (q = last + 1, X,
    if (q % 3 != 2, next);
    ok = 1;
    for (i = 1, #S, if (q % S[i] == 1, ok = 0; break));
    if (!ok, next);
    l = -log(1 - 1. / q);
    cnt++; acc += l;
    if (cnt <= RMAX, fq[cnt] = q; fl[cnt] = l; fc[cnt] = acc);
    if (cnt == m && lp + acc < LV - EPS, return(0));
    if (cnt >= m,
      \\ child number t = cnt - m + 1: its own factor and the m - 1 candidates after it
      t = cnt - m + 1;
      if (t > RMAX, error("RMAX too small"));
      cb = lp + fl[t] + (acc - fc[t]);
      if (cb < LV - EPS, return(vector(t - 1, i, fq[i])))));
  error("X too small");
}

visit(S, lp) = {
  my(m = K - #S, kids, last = if (#S, S[#S], 2));
  nodes++; bydepth[#S + 1]++;
  if (lp >= LV - EPS, result = Str("possible: ", S); return(1));
  if (m == 0, return(0));
  kids = pass(S, last, m, lp);
  if (kids == 0, return(0));
  printf("   node %d, S = %s, children %s\n", nodes, S, kids);
  for (j = 1, #kids,
    if (visit(concat(S, [kids[j]]), lp - log(1 - 1. / kids[j])), return(1)));
  0;
}

{
  my(t0 = getabstime());
  visit([], 0.);
  printf("K = %d, V = %s (%.12f), primes = 2 mod 3 up to %d: %s\n", K, V, V * 1., X, result);
  printf("nodes %d by depth %s, %.0f s\n", nodes, bydepth[1 .. 12], (getabstime() - t0) / 1000.);
}
quit;
