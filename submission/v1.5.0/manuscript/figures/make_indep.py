#!/usr/bin/env python3
"""Writes fig_indep.tex: the primes from 5 to 89 with an arc from p to q whenever p divides q - 1, and the
independent set chosen one prime at a time (Section 2.1 of the paper), with the product of p/(p-1) after each
chosen prime."""
from fractions import Fraction

P = [p for p in range(5, 90) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
arcs = [(p, q) for p in P for q in P if q > p and (q - 1) % p == 0]
chosen, prod, prods = [], Fraction(1), {}
for q in P:
    if all((q - 1) % p for p in chosen):
        chosen.append(q)
        prod *= Fraction(q, q - 1)
        prods[q] = prod
first2 = next(q for q in chosen if prods[q] > 2)
assert first2 == 83 and chosen.index(83) == 10

DX = 0.72
x = {p: i * DX for i, p in enumerate(P)}
# where each arc meets its primes: arcs arriving at a prime use the left half of its disc, the longest nearest the
# centre, and arcs leaving it use the right half, the longest nearest the centre, so that no two arcs touch
end = {}
for p in P:
    inc = sorted((a for a in arcs if a[1] == p), key=lambda a: x[a[1]] - x[a[0]])
    out_ = sorted((a for a in arcs if a[0] == p), key=lambda a: -(x[a[1]] - x[a[0]]))
    for j, a in enumerate(inc):
        end[a, 1] = x[p] - 0.10 + 0.10 * (j + 1) / (len(inc) + 1) if out_ else x[p] - 0.09 + 0.18 * (j + 1) / (len(inc) + 1)
    for j, a in enumerate(out_):
        end[a, 0] = x[p] + 0.10 * (j + 1) / (len(out_) + 1) if inc else x[p] - 0.09 + 0.18 * (j + 1) / (len(out_) + 1)
out = ["\\begin{tikzpicture}[font=\\small]"]
top = 0
for p, q in sorted(arcs, key=lambda a: -(x[a[1]] - x[a[0]])):
    span = x[q] - x[p]
    h = 0.32 + 0.21 * span
    top = max(top, h)
    col = "blue!65!black" if p in chosen else "black!35"
    a, b = end[(p, q), 0], end[(p, q), 1]
    out.append(f"\\draw[{col}, line width=0.7pt, overlay] ({a:.3f},0.15) .. controls ({a:.3f},{h * 4 / 3:.3f}) "
               f"and ({b:.3f},{h * 4 / 3:.3f}) .. ({b:.3f},0.15);")
out.append(f"\\path (0,0) -- (0,{top + 0.05:.3f});")
out.append(f"\\draw[black!30] (-0.3,0) -- ({x[P[-1]] + 0.3:.3f},0);")
for p in P:
    if p in chosen:
        out.append(f"\\fill[blue!65!black] ({x[p]:.3f},0) circle (0.13);")
    else:
        out.append(f"\\draw[black!55, fill=white, line width=0.6pt] ({x[p]:.3f},0) circle (0.13);")
    out.append(f"\\node[anchor=north] at ({x[p]:.3f},-0.2) {{${p}$}};")
for q in chosen:
    v = float(prods[q])
    style = "font=\\scriptsize\\bfseries, text=blue!65!black" if q == first2 else "font=\\scriptsize, text=black!70"
    out.append(f"\\node[anchor=north, {style}] at ({x[q]:.3f},-0.72) {{${v:.2f}$}};")
out.append(f"\\node[anchor=east, font=\\scriptsize, text=black!70] at (-0.3,-0.42) {{$q$}};")
out.append(f"\\node[anchor=east, font=\\scriptsize, text=black!70] at (-0.3,-0.9) "
           f"{{$\\prod_{{p\\in S,\\ p\\le q}}p/(p-1)$}};")
# legend
ly = -1.75
leg = [
    (0.0, "\\fill[blue!65!black] (0,0) circle (0.13);", "$q\\in S$: no $p\\in S$ below $q$ divides $q-1$"),
    (8.1, "\\draw[black!55, fill=white, line width=0.6pt] (0,0) circle (0.13);", "$q\\notin S$: some $p\\in S$ divides $q-1$"),
]
for x0, sym, txt in leg:
    out.append(f"\\begin{{scope}}[shift={{({x0:.2f},{ly})}}]{sym}\\node[anchor=west, font=\\scriptsize] at (0.25,0) {{{txt}}};\\end{{scope}}")
ly2 = ly - 0.5
leg2 = [
    (0.0, "blue!65!black", "arc from $p\\in S$ to $q$, where $p\\mid q-1$"),
    (8.1, "black!35", "arc from $p\\notin S$ to $q$, where $p\\mid q-1$"),
]
for x0, col, txt in leg2:
    out.append(f"\\draw[{col}, line width=0.7pt] ({x0 - 0.15:.2f},{ly2 - 0.08:.2f}) .. controls ({x0 - 0.15:.2f},{ly2 + 0.14:.2f}) "
               f"and ({x0 + 0.15:.2f},{ly2 + 0.14:.2f}) .. ({x0 + 0.15:.2f},{ly2 - 0.08:.2f});")
    out.append(f"\\node[anchor=west, font=\\scriptsize] at ({x0 + 0.25:.2f},{ly2:.2f}) {{{txt}}};")
out.append("\\end{tikzpicture}")
open("fig_indep.tex", "w").write("\n".join(out) + "\n")
print("chosen:", chosen)
print("arcs:", arcs)
print("products:", {q: round(float(v), 5) for q, v in prods.items()})
