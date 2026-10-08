\\ search.gp with progress output, used to probe the case s = 8 of the search of
\\ Section 6.3 (see "Where the search is hard" in the paper). It prints a line every
\\ 5000 nodes and every 200000 admissible children of one node; otherwise it is
\\ search.gp line for line.
\\ Usage: printf 's = 8\n\\r search_probe.gp\n' | gp -q
\\ The run in logs/search_probe_s8.log was stopped after about five minutes, at a
\\ node of depth 12 with more than 10^6 children; the search for s = 8 is not complete.

default(parisize, 10^9);
if (type(s) != "t_INT", s = 4);
BIG = 10^30;

thr(i) = if (i >= s, 2^(2^(i - s)), 1);

\\ least m >= 1 with P*m^e >= T
minroot(P, e, T) = {
  my(q, m);
  if (P >= T, return(1));
  q = ceil(T / P);
  m = sqrtnint(q, e);
  if (m^e < q, m++);
  m;
}

\\ m-th odd prime above p, or the lower bound p + 2m beyond 2*10^7
primeafter(p, m) = {
  my(q = max(p, 2));
  if (q > 2*10^7, return(p + 2*m));
  for (t = 1, m, q = nextprime(q + 1));
  q;
}

\\ upper bound for prod_{i=j+1}^{k} p_i/(p_i-1) over all k >= j+1, given
\\ the prefix (length j, product P) and p_{j+1} >= first
extbound(j, P, first) = {
  my(best = first / (first - 1), prod = 1, i = j + 1, root, b, cur, m = 0, exact = (first < 2*10^7));
  cur = first;
  while (1,
    root = minroot(P, i - j, thr(i));
    b = max(cur, root);
    if (root > BIG && i >= j + 3,
      return(max(best, prod * (1 + 16 / (root - 2)))));
    prod *= b / (b - 1);
    best = max(best, prod * (b + 2) / (b + 1));
    i++;
    m++;
    if (exact, cur = nextprime(cur + 1); if (cur >= 2*10^7, exact = 0));
    if (!exact, cur = first + 2*m));
}

mneed(S, r) = {
  my(lo = floor(r) + 1, m);
  if (#S && S[1] == 3,
    m = max(4, lo); while (m % 3 != 1, m++); return(m));
  max(2, lo);
}

adm(S, q) = {
  for (t = 1, #S, if ((q - 1) % S[t] == 0, return(0)));
  1;
}

search() = {
  my(e, S, P, F, j, r, need, last, first, q, lo, top, M, D, qk, kids, stack, qc, need2, T, xm, x1, x2, Vq);
  
  \\ stack of prefixes; each entry [S, P, F]
  stack = List([[[], 1, 1]]);
  while (#stack,
    e = stack[#stack];
    listpop(stack);
    S = e[1]; P = e[2]; F = e[3]; j = #S;
    r = P / F; need = mneed(S, r);
    last = if (j, S[j], 1);
    first = if (j, nextprime(last + 1), 3);
    if (r * extbound(j, P, first) <= need, next);
    \\ deficit form of Nielsen's lemma, with the smallest admissible M
    if (j + 1 >= s && need * F * (P + 1) / (need * F - P) < 2^(2^(j + 1 - s)), light++; next);
    nodes++; maxdepth = max(maxdepth, j); if (nodes % 5000 == 0, print("progress nodes ", nodes, " stack ", #stack, " S ", S, " t ", gettime()));
    if (j >= 1,
      top = r * (last + 2) / (last + 1);
      M = need;
      while (M < top,
        if (!(S[1] == 3 && M % 3 != 1),
          tests++;
          D = M * F - P;
          if ((M * F - 1) % D == 0,
            qk = (M * F - 1) / D;
            if (qk > last && isprime(qk) && adm(S, qk),
              found++; print("LEHMER ", concat(S, [qk]), " M=", M))));
        M++));
    q = first;
    lo = ceil(thr(j + 1) / P);
    if (lo > q, q = nextprime(lo));
    kids = List();
    D = need * F - P;
    qc = (need * F) \ D;
    need2 = need + 1; if (#S && S[1] == 3, while (need2 % 3 != 1, need2++));
    \\ (i) q <= qc: children need M >= need2; one test settles the range when it fails
    if (q <= qc && r * extbound(j, P, q) > need2,
      while (q <= qc && r * extbound(j, P, q) > need2,
        if (adm(S, q), listput(kids, q); if (#kids % 200000 == 0, print("  bigkids ", #kids, " j ", j, " S ", S, " q ", q)));
        q = nextprime(q + 1)));
    if (q <= qc, q = nextprime(qc + 1));
    \\ (ii) q > qc: the child is light unless V(q) >= 2^(2^(j+2-s)), where
    \\ V(q) = need*F*(q-1)*(P*q+1)/(D*q - need*F); find where V(q) >= T by bisection
    if (j + 2 >= s,
      T = 2^(2^(j + 2 - s));
      Vq = ((x) -> need * F * (x - 1) * (P * x + 1) - T * (D * x - need * F));
      \\ Vq is a convex quadratic in x: nonnegative outside [x1, x2]; locate its minimum
      xm = max(q, ceil((T * D - need * F + need * F * P) / (2 * need * F * P)));
      if (Vq(xm) < 0,
        \\ heavy for q <= x1 and for q >= x2; bisection for x1 in [q, xm] and x2 >= xm
        my(lo1 = q, hi1 = xm, lo2 = xm, hi2 = 2 * xm + 2);
        if (Vq(lo1) < 0, x1 = lo1 - 1,
          while (hi1 - lo1 > 1, my(mid = (lo1 + hi1) \ 2); if (Vq(mid) >= 0, lo1 = mid, hi1 = mid)); x1 = lo1);
        while (Vq(hi2) < 0, hi2 *= 2);
        while (hi2 - lo2 > 1, my(mid = (lo2 + hi2) \ 2); if (Vq(mid) >= 0, hi2 = mid, lo2 = mid));
        x2 = hi2;
        while (q <= x1 && r * extbound(j, P, q) > need,
          if (adm(S, q), listput(kids, q); if (#kids % 200000 == 0, print("  bigkids ", #kids, " j ", j, " S ", S, " q ", q)));
          q = nextprime(q + 1));
        if (q < x2, q = nextprime(x2))));
    while (r * extbound(j, P, q) > need,
      if (adm(S, q), listput(kids, q); if (#kids % 200000 == 0, print("  bigkids ", #kids, " j ", j, " S ", S, " q ", q)));
      q = nextprime(q + 1));
    forstep (t = #kids, 1, -1,
      listput(stack, [concat(S, [kids[t]]), P * kids[t], F * (kids[t] - 1)])));
  
}

nodes = 0; maxdepth = 0; found = 0; tests = 0; light = 0;
search();
print("s = ", s, " nodes ", nodes, " maxdepth ", maxdepth, " last-prime tests ", tests, " light ", light, " Lehmer numbers found ", found);

