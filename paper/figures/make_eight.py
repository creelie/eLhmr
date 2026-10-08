#!/usr/bin/env python3
"""Writes fig_eight.tex: the eight-prime case of the companion equation.
Left: the 10458 prefixes (3, p_2, ..., p_5) by the width of the interval for p_6.
Right: processor time per admissible p_6 = s under the prefix 3, 5, 17, 257, 65537, against the modulus c = s - 2^32,
one point per piece of the run (from the journal data/companion8/journal.jsonl)."""
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)
import lastthree as L

fr = [x for x in L.frontier(8, 3, 2, 1, +1, 3) if 3 in x[0]]
hist = [0] * 10
for c, A, B, lo, hi in fr:
    w = hi - lo
    hist[0 if w < 1 else int(math.log10(w))] += 1
K = 2 ** 32
pts_f, pts_s = [], []
for l in open(os.path.join(ROOT, "data", "companion8", "journal.jsonl")):
    if not l.strip(): continue
    r = json.loads(l)
    if len(r["keys"]) != 1 or not r["keys"][0].startswith("3,5,17,257,65537:") or r["nx"] == 0: continue
    a, b = map(int, r["keys"][0].split(":")[1].split("-"))
    c = math.sqrt(max(a - K, 1) * (b - K))
    us = (r["scan_sec"] + r["gp_sec"]) / r["nx"] * 1e6
    (pts_f if r["ndef"] > 0.5 * r["nx"] else pts_s).append((math.log10(c), math.log10(us)))
coords = lambda P: " ".join(f"({x:.4f},{y:.4f})" for x, y in sorted(P))
out = r"""\begin{tikzpicture}
\begin{axis}[name=left, width=0.50\textwidth, height=0.42\textwidth, ybar, bar width=6pt, ymode=log, log origin=infty,
  ymin=0.5, ymax=3e4, xmin=-0.7, xmax=9.7,
  xtick={0,...,9}, xticklabels={$10^0$,$10^1$,$10^2$,$10^3$,$10^4$,$10^5$,$10^6$,$10^7$,$10^8$,$10^9$},
  x tick label style={font=\tiny}, y tick label style={font=\scriptsize}, axis line style={black!70},
  ylabel={\small number of prefixes}, xlabel={\small width of the interval for $p_6$},
  grid=major, grid style={black!8},
  nodes near coords={\pgfmathprintnumber[fixed, precision=0, 1000 sep={\,}]{\pgfplotspointmeta}},
  nodes near coords style={font=\tiny, text=black!75, anchor=south}, point meta=rawy]
\addplot[fill=orange!75!red, draw=black!55] coordinates {""" + " ".join(f"({i},{h})" for i, h in enumerate(hist)) + r"""};
\end{axis}
\begin{axis}[at={(left.east)}, anchor=west, xshift=16mm, width=0.50\textwidth, height=0.42\textwidth,
  xmin=4.7, xmax=10.2, ymin=-1.3, ymax=4.6, axis line style={black!70},
  xtick={5,6,7,8,9,10}, xticklabels={$10^5$,$10^6$,$10^7$,$10^8$,$10^9$,$10^{10}$},
  ytick={-1,0,1,2,3,4}, yticklabels={$10^{-1}$,$10^0$,$10^1$,$10^2$,$10^3$,$10^4$},
  x tick label style={font=\scriptsize}, y tick label style={font=\scriptsize},
  xlabel={\small modulus $c=p_6-2^{32}$}, ylabel={\small microseconds per $p_6$},
  grid=major, grid style={black!8},
  legend style={font=\scriptsize, draw=none, fill=white, fill opacity=0.85, text opacity=1, at={(0.03,0.03)}, anchor=south west}, legend cell align=left]
\addplot[only marks, mark=*, mark size=1.3pt, color=orange!80!red] coordinates {""" + coords(pts_f) + r"""};
\addplot[only marks, mark=*, mark size=1.3pt, color=blue!55!teal] coordinates {""" + coords(pts_s) + r"""};
\draw[black!60, dashed] (axis cs:9.633,-1.3) -- (axis cs:9.633,4.6);
\node[font=\tiny, text=black!70, anchor=south, rotate=90] at (axis cs:9.633,-0.2) {$c=2^{32}$};
\legend{$N$ factored, sums and trial division}
\end{axis}
\end{tikzpicture}
"""
open(os.path.join(HERE, "fig_eight.tex"), "w").write(out)
print(len(pts_f), len(pts_s), hist)
