#!/usr/bin/env python3
"""Writes fig_products.tex: the product of p/(p-1) over the first k primes of three lists, and over the independent
sets chosen one prime at a time from two of them (Section 2.1 of the paper), for the primes below 2*10^8.
Also prints the crossings quoted in the text."""
import math
import numpy as np

L = 2 * 10 ** 8
s = np.ones(L + 1, dtype=bool); s[:2] = False
for i in range(2, int(L ** 0.5) + 1):
    if s[i]:
        s[i * i::i] = False
P = np.nonzero(s)[0]
YMAX = 4.5


def sample(seq, start=0.0):
    """points (k, product) of the products over the first k terms of seq, with log(start) the initial log"""
    pts, lp, nxt = [], start, 1
    for k, p in enumerate(seq, 1):
        lp += math.log1p(1 / (p - 1))
        if k <= 60 or k >= nxt:
            pts.append((k, math.exp(lp)))
            nxt = max(k + 1, math.ceil(k * 1.04))
        if math.exp(lp) > YMAX + 0.2:
            break
    return pts


def greedy(Q):
    """the independent set chosen one prime at a time from Q (increasing): each prime not = 1 modulo a chosen one"""
    exc = np.zeros(L + 1, dtype=bool)
    out = []
    for p in Q.tolist():
        if not exc[p]:
            out.append(p)
            exc[1 + p::p] = True
    return out


def first(seq, v):
    """the least k with the product over the first k terms of seq at least v"""
    lg = np.cumsum(np.log1p(1 / (np.array(seq, dtype=float) - 1)))
    return int(np.argmax(lg >= math.log(v))) + 1


Q5 = P[P >= 5]
Q2 = Q5[Q5 % 3 == 2]
first5 = sample(Q5[:2000].tolist())
odd = sample(P[P >= 3][:100].tolist())
mod3 = sample([3] + Q2[:200000].tolist())
G5 = greedy(Q5)
G2 = greedy(Q2)
lg5 = np.cumsum(np.log1p(1 / (np.array(G5, dtype=float) - 1)))
lg2 = np.cumsum(np.log1p(1 / (np.array(G2, dtype=float) - 1)))
k2 = int(np.argmax(lg5 >= math.log(2))) + 1
k3 = int(np.argmax(lg5 >= math.log(3))) + 1
c = (first(Q5[:100], 2), first(Q5[:100], 3), first(P[1:100], 3), first([3] + Q2[:2000].tolist(), 4))
print(f"primes from 5 on: product passes 2 at k = {c[0]}, 3 at k = {c[1]}")
print(f"odd primes: passes 3 at k = {c[2]};  3 and primes = 2 mod 3: passes 4 at k = {c[3]}")
print(f"independent from 5 on: {len(G5)} primes below {L}, product {math.exp(lg5[-1]):.6f}; "
      f"passes 2 at the {k2}-th ({G5[k2 - 1]}), 3 at the {k3}-th ({G5[k3 - 1]}); "
      f"products {math.exp(lg5[k3 - 2]):.10f}, {math.exp(lg5[k3 - 1]):.10f}")
print(f"independent primes = 2 mod 3: {len(G2)} primes below {L}, product {math.exp(lg2[-1]):.6f} "
      f"(with 3: {1.5 * math.exp(lg2[-1]):.6f})")
assert c == (7, 33, 8, 1540)
assert (k2, G5[k2 - 1], k3, G5[k3 - 1]) == (11, 83, 100470, 5160959)


def gsample(lg, shift, start):
    pts, nxt = [], 1
    for k in range(1, len(lg) + 1):
        if k <= 60 or k >= nxt or k == len(lg):
            pts.append((k + shift, math.exp(start + lg[k - 1])))
            nxt = max(k + 1, math.ceil(k * 1.04))
    return pts


g5 = gsample(lg5, 0, 0.0)
g2 = gsample(lg2, 1, math.log(1.5))
g2 = [(1, 1.5)] + g2


def coords(pts):
    return " ".join(f"({k},{y:.5f})" for k, y in pts)


BL, OR, TE = "blue!65!black", "orange!85!black", "teal!70!black"
XMAX = "4e8"
AXIS = """width=\\textwidth, height=0.37\\textwidth,
  xmin=1, xmax=%s, ymin=1, ymax=%s, clip=true,
  xtick={1,10,100,1000,1e4,1e5,1e6,1e7,1e8},
  xticklabels={$1$,$10$,$10^2$,$10^3$,$10^4$,$10^5$,$10^6$,$10^7$,$10^8$},
  ytick={1,2,3,4},
  tick label style={font=\\scriptsize}, label style={font=\\small},
  ylabel={$\\prod p/(p-1)$ over the $k$ primes},
  grid=major, grid style={black!7}, axis line style={black!45},
  legend style={at={(0.985,0.05)}, anchor=south east, draw=black!25, fill=white, font=\\scriptsize},
  legend cell align=left""" % (XMAX, YMAX)


def hlines(ys):
    return [f"\\addplot[black!35, dashed, forget plot] coordinates {{(1,{y}) ({XMAX},{y})}};" for y in ys]


def mark(col, pts, hollow=False):
    style = "mark=o, mark size=2.6pt, very thick" if hollow else "mark=*, mark size=2.2pt"
    return f"\\addplot[only marks, {style}, {col}, forget plot] coordinates {{{' '.join(f'({k},{y})' for k, y in pts)}}};"


def label(col, anchor, x, y, text):
    return f"\\node[font=\\scriptsize, anchor={anchor}, {col}] at (axis cs:{x},{y}) {{{text}}};"


y7 = dict(first5)[7]; y33 = dict(first5)[33]; y8 = dict(odd)[8]
out = ["\\begin{tikzpicture}", f"\\begin{{semilogxaxis}}[name=top, {AXIS},",
       "  title={(a) primes $p\\ge5$, for $3\\nmid n$, and the odd primes}, title style={font=\\small}]"]
out += hlines((2, 3))
out.append(f"\\addplot[thick, {BL}] coordinates {{{coords(first5)}}};")
out.append("\\addlegendentry{the first primes from $5$ on}")
out.append(f"\\addplot[thick, {BL}, densely dashed] coordinates {{{coords(g5)}}};")
out.append("\\addlegendentry{independent primes from $5$ on, chosen one at a time}")
out.append(f"\\addplot[thick, {OR}] coordinates {{{coords(odd)}}};")
out.append("\\addlegendentry{the first odd primes}")
out.append(mark(BL, [(7, f"{y7:.5f}"), (33, f"{y33:.5f}"), (k3, 3)]))
out.append(mark(OR, [(8, f"{y8:.5f}")]))
out.append(mark(BL, [(16001, 3)], hollow=True))
out.append(label(BL, "north west", 8.6, 1.86, "$k=7$"))
out.append(label(OR, "south east", 7.4, 3.10, "$k=8$"))
out.append(label(BL, "north west", 36, 2.94, "$k=33$"))
out.append(label(BL, "south", 16001, 3.09, "$16001$, Proposition 2.5(i)"))
out.append(label(BL, "north west", f"{k3 * 1.12:.0f}", 2.94, f"$k={k3}$"))
out.append("\\end{semilogxaxis}")
out.append(f"\\begin{{semilogxaxis}}[at={{(top.below south west)}}, anchor=north west, yshift=-0.9cm, {AXIS},")
out.append("  title={(b) $3$ and the primes $p\\equiv2\\pmod 3$, for $3\\mid n$}, title style={font=\\small},")
out.append("  xlabel={number $k$ of primes}]")
out += hlines((2, 3, 4))
out.append(f"\\addplot[thick, {TE}] coordinates {{{coords(mod3)}}};")
out.append("\\addlegendentry{$3$ and the first primes $p\\equiv2\\pmod 3$}")
out.append(f"\\addplot[thick, {TE}, densely dashed] coordinates {{{coords(g2)}}};")
out.append("\\addlegendentry{$3$ and independent primes $p\\equiv2\\pmod 3$, chosen one at a time}")
out.append(mark(TE, [(1540, 4)]))
out.append(mark(TE, [(100000002, 4)], hollow=True))
out.append(label(TE, "south east", 1400, 4.07, "$k=1540$"))
out.append(label(TE, "south east", 100000002 * 1.6, 4.09, "$10^8+2$, Proposition 2.5(ii)"))
out.append("\\end{semilogxaxis}\n\\end{tikzpicture}")
open("fig_products.tex", "w").write("\n".join(out) + "\n")
