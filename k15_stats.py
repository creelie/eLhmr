#!/usr/bin/env python3
"""Statistics for the paper (Sections 5 and 9).

(a) For every one of the 33,865,004 pairs (prefix of 12 primes, admissible p_13 = s) of the case k = 15:
    the modulus c = 2B' - A' and N = 2A'B' - c of the two-prime problem, and a histogram of log10(c^3/N).
    When c^3 > N the divisors of N in a residue class modulo c number at most 11 (Lenstra) and the lattice
    method needs only a few boxes; the factored instances sit in the far left tail.
(b) The totals of the runs recorded in data/k15/run_*.jsonl (for program C, 'tested' counts square tests and
    'direct' trial divisions).
(c) The frontier at depth 12 for k = 16 (four primes still to choose): number of prefixes and the widths of
    the intervals for p_13, the exact number of admissible p_13, and a first-order count of the admissible pairs
    (p_13, p_14) that the three-prime completion would have to treat, with the sizes of their N and c^3/N.
Output: data/k15/stats.json.  Runtime: a few minutes."""
import sys, os, json, math, gzip, collections
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lastthree as L

out = {}
fr = json.load(open("data/k15/frontier.json"))
hist = collections.Counter(); ns = 0; lenstra = 0; minlog = 1e9; argmin = None; nd = [10**9, 0]
for chosen, lo, hi in fr:
    chosen = tuple(chosen)
    A = 1; B = 1
    for p in chosen: A *= p; B *= p - 1
    C = 2 * B - A
    ss = L.primes_in(lo, hi); ss = ss[L.admissible_mask(ss, chosen)]
    if len(ss) == 0: continue
    s_first = -((-2 * B) // C)                      # least integer with C s - 2B >= 0
    rho0 = C * s_first - 2 * B                      # exact, 0 <= rho0 < C
    d = (ss - s_first).astype(np.float64)
    c = d * float(C) + float(rho0)                  # c = C s - 2B, without cancellation
    assert np.all(c > 0)
    logN = math.log10(2 * A * B) + np.log10(ss.astype(np.float64)) + np.log10(ss.astype(np.float64) - 1)
    x = 3 * np.log10(c) - logN
    ns += len(ss); lenstra += int(np.sum(x > 0))
    if float(x.min()) < minlog: minlog = float(x.min()); argmin = (list(chosen), int(ss[int(np.argmin(x))]))
    for s_ in (int(ss[0]), int(ss[-1])):            # N increases with s: the extremes of the digits of N
        A_ = A * s_; B_ = B * (s_ - 1)
        for e_ in (-1, 1):
            k_ = len(str(2 * A_ * B_ + e_ * (2 * B_ - A_))); nd = [min(nd[0], k_), max(nd[1], k_)]
    for b, k in zip(*np.unique(np.floor(x).astype(int), return_counts=True)): hist[int(b)] += int(k)
out["k15_pairs"] = ns
out["k15_lenstra_regime"] = lenstra
out["k15_min_log10_c3_over_N"] = minlog; out["k15_argmin_c3_over_N"] = argmin; out["k15_digits_N"] = nd
out["k15_hist_log10_c3_over_N"] = dict(sorted(hist.items()))
print(f"(a) {ns} pairs; c^3 > N for {lenstra}; min log10(c^3/N) = {minlog:.2f} at prefix {argmin[0]}, s = {argmin[1]}; "
      f"N has {nd[0]} to {nd[1]} digits")
print("    histogram of floor(log10(c^3/N)):", dict(sorted(hist.items())))

runs = {}
for name in ("run_A", "run_A_plus", "run_B", "run_B_plus", "run_C", "run_C_plus"):
    path = f"data/k15/{name}.jsonl"
    if os.path.exists(path): f = open(path)
    elif os.path.exists(path + ".gz"): f = gzip.open(path + ".gz", "rt")     # archived runs are gzipped
    else: continue
    rows = [json.loads(l) for l in f]
    keys = ("n_s", "boxes", "tested", "direct", "factored", "found", "sec")
    tot = {k: sum(r.get(k, 0) for r in rows) for k in keys}
    tot["tasks"] = len({tuple(r["task"]) for r in rows}); tot["sols"] = sum(len(r["sols"]) for r in rows)
    tot["cands"] = sum(len(r["cands"]) for r in rows)
    runs[name] = tot
    print(f"(b) {name}: {tot}")
out["runs"] = runs

fr16 = L.frontier(16, 5, 2, 1, -1, 4)
w16 = [hi - lo for c, A, B, lo, hi in fr16]
h16 = collections.Counter(int(math.floor(math.log10(w))) if w > 0 else 0 for w in w16)
# For every admissible p_13 = s the shortfall d = C_13/A_13 is computed as in (a).  With three primes still to
# choose, Proposition 3.2 puts p_14 in about [p_0, 3/d] with p_0 = (1 + d)/d (and p_14 > s), and that interval
# holds about (length) F / log(p_0) admissible primes, where F = prod (1 - 1/(q - 1)) over the thirteen chosen
# primes q is the share of primes that pass the congruence prune.  For p_14 = p_0 + y the next shortfall is
# d_14 = d y / (p_0 + y), and the two-prime problem that follows has c^3/N ~ A_14 d_14^3 ~ A_13 d^5 y^3, so that
# c^3/N < theta for y below (theta / (A_13 d^5))^(1/3).  All of this is a first-order count.
thetas = [1.0, 1e-3, 1e-6, 1e-9, 1e-12]
primes13 = 0; adm13 = 0; pairs_all = 0.0; pairs_adm = 0.0; tail = [0.0] * len(thetas)
dig_lo = 1e9; dig_hi = 0.0; dig_w = 0.0; top = []
for chosen, A, B, lo, hi in fr16:
    C = 2 * B - A
    ss = L.primes_in(lo, hi); primes13 += len(ss)
    if len(ss) == 0: continue
    F = 1.0
    for q in chosen: F *= 1 - 1 / (q - 1)
    mask = L.admissible_mask(ss, chosen); adm13 += int(mask.sum())
    s_first = -((-2 * B) // C); rho0 = C * s_first - 2 * B
    sf = ss.astype(np.float64)
    A13 = float(A) * sf
    d = ((sf - s_first) * float(C) + float(rho0)) / A13
    p0 = (1 + d) / d
    lo14 = np.maximum(p0, sf + 1); hi14 = 1 / ((1 + d) ** (1 / 3) - 1) + 1
    ok = hi14 > lo14
    length = np.where(ok, hi14 - lo14, 0.0)
    per_len = 1 / np.log(np.sqrt(lo14 * np.maximum(hi14, lo14)))           # primes per unit length
    pairs_all += float((length * per_len).sum())
    dens = np.where(mask, F * (1 - 1 / (sf - 1)) * per_len, 0.0)           # admissible pairs per unit length
    e = float((length * dens).sum()); pairs_adm += e; top.append((e, list(chosen), hi - lo))
    y0 = lo14 - p0; ymax = hi14 - p0
    for i, th in enumerate(thetas):
        yth = (th * (1 + d) ** 2 / (A13 * d ** 5)) ** (1 / 3)
        tail[i] += float((np.clip(np.minimum(yth, ymax) - y0, 0, None) * np.where(ok, dens, 0.0)).sum())
    if ok.any():                                                            # log10 N ~ log10(2 A B s^2 p_14^2)
        l0 = math.log10(2 * A * B) + 2 * np.log10(sf[ok])
        a_, b_ = l0 + 2 * np.log10(lo14[ok]), l0 + 2 * np.log10(hi14[ok])
        dig_lo = min(dig_lo, float(a_.min())); dig_hi = max(dig_hi, float(b_.max()))
        dig_w += float((length[ok] * dens[ok] * (a_ + b_) / 2).sum())
top.sort(reverse=True)
out["k16_depth12_nodes"] = len(fr16); out["k16_total_width"] = sum(w16)
out["k16_hist_log10_width"] = dict(sorted(h16.items()))
out["k16_primes_p13"] = primes13; out["k16_admissible_p13"] = adm13
out["k16_estimated_pairs_of_primes"] = pairs_all; out["k16_estimated_pairs"] = pairs_adm
out["k16_estimated_pairs_c3_below_theta_N"] = {f"{th:g}": x for th, x in zip(thetas, tail)}
out["k16_log10_N"] = {"min": dig_lo, "max": dig_hi, "pair_weighted_mean": dig_w / pairs_adm}
out["k16_top"] = [(e / pairs_adm, c, w) for e, c, w in top[:5]]
sec15 = runs.get("run_C", {}).get("sec", 0) / max(1, ns)
print(f"(c) k=16: {len(fr16)} nodes at depth 12, total width {sum(w16):.3e}; {primes13} primes p_13, {adm13} admissible")
print("    histogram of floor(log10(width)):", dict(sorted(h16.items())))
print(f"    pairs (p_13, p_14) of primes ~ {pairs_all:.2e}; admissible pairs ~ {pairs_adm:.2e}, "
      f"{top[0][0] / pairs_adm:.1%} of them from the prefix ending in {top[0][1][-1]}")
print("    admissible pairs with c^3/N < theta:", {f"{th:g}": f"{x:.1e}" for th, x in zip(thetas, tail)})
print(f"    log10 N from {dig_lo:.1f} to {dig_hi:.1f}, pair-weighted mean {dig_w / pairs_adm:.1f}")
if sec15: print(f"    at the average speed of program C for k = 15 ({sec15 * 1e6:.1f} microseconds per problem): "
                f"{pairs_adm * sec15:.1e} s for the admissible pairs")
json.dump(out, open("data/k15/stats.json", "w"), indent=1)
