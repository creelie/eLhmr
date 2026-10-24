#!/usr/bin/env python3
"""Writes fig_profile.tex: the number of nodes at each depth of the search for k = 7..15 (logs/walls.log, Table 2
and Section 5.2 of the paper), as a grid of cells shaded by the decimal logarithm of the count."""
import math
prof = {
    7: [1, 2, 3, 1, 1, 0],
    8: [1, 3, 4, 4, 3, 2, 1],
    9: [1, 4, 6, 5, 7, 4, 1, 1],
    10: [1, 4, 8, 10, 9, 5, 3, 1, 1],
    11: [1, 4, 10, 15, 14, 9, 6, 3, 4, 7],
    12: [1, 5, 12, 19, 17, 14, 8, 7, 12, 29, 63],
    13: [1, 6, 15, 23, 25, 19, 12, 17, 30, 60, 154, 730],
    14: [1, 6, 16, 27, 29, 23, 22, 33, 58, 127, 335, 1654, 29631],
    15: [1, 6, 18, 30, 34, 37, 41, 56, 103, 218, 616, 3227, 55125, 33865004],
}
W, H = 1.02, 0.56
# a perceptually ordered scale from pale yellow to dark blue (viridis-like), indexed by log10(count) in [0, 7.6]
stops = [(0.00, (253, 231, 37)), (0.25, (94, 201, 98)), (0.50, (33, 145, 140)), (0.75, (59, 82, 139)), (1.00, (68, 1, 84))]
def colour(v):
    t = min(max(v / 7.6, 0.0), 1.0)
    for (a, ca), (b, cb) in zip(stops, stops[1:]):
        if a <= t <= b:
            u = (t - a) / (b - a)
            return tuple(round(x + (y - x) * u) for x, y in zip(ca, cb))
def label(n):
    if n >= 10 ** 6:
        e = int(math.log10(n)); m = n / 10 ** e
        return f"${m:.1f}\\!\\cdot\\!10^{{{e}}}$"
    return f"{n:,}".replace(",", "\\,")
out = ["\\begin{tikzpicture}[font=\\scriptsize]"]
ks = sorted(prof)
for row, k in enumerate(reversed(ks)):
    y = row * H
    out.append(f"\\node[anchor=east] at (-0.12,{y + H / 2:.3f}) {{$k={k}$}};")
    for j, n in enumerate(prof[k]):
        x = j * W
        if n == 0:
            out.append(f"\\draw[black!25, fill=white] ({x:.3f},{y:.3f}) rectangle ({x + W:.3f},{y + H:.3f});")
            out.append(f"\\node[text=black!60] at ({x + W / 2:.3f},{y + H / 2:.3f}) {{0}};")
            continue
        r, g, b = colour(math.log10(n))
        out.append(f"\\definecolor{{c}}{{RGB}}{{{r},{g},{b}}}")
        dark = (0.299 * r + 0.587 * g + 0.114 * b) < 140
        style = "draw=white, line width=0.6pt, fill=c" + (", pattern color=white" if False else "")
        out.append(f"\\fill[c] ({x:.3f},{y:.3f}) rectangle ({x + W:.3f},{y + H:.3f});")
        out.append(f"\\draw[white, line width=0.8pt] ({x:.3f},{y:.3f}) rectangle ({x + W:.3f},{y + H:.3f});")
        tc = "white" if dark else "black!85"
        out.append(f"\\node[text={tc}] at ({x + W / 2:.3f},{y + H / 2:.3f}) {{{label(n)}}};")
# the last cell of k = 15 counts choices of p_13, treated by Section 4: frame it
y15 = 0
out.append(f"\\draw[black!80, line width=0.9pt] ({13 * W:.3f},{y15:.3f}) rectangle ({14 * W:.3f},{y15 + H:.3f});")
for j in range(14):
    out.append(f"\\node at ({j * W + W / 2:.3f},-0.25) {{{j}}};")
out.append(f"\\node at ({7 * W:.3f},-0.68) {{\\small depth $j$, the number of primes chosen}};")
# colour bar
bx, by = 0.0, len(ks) * H + 0.35
for i in range(76):
    v = i / 10
    r, g, b = colour(v)
    out.append(f"\\definecolor{{c}}{{RGB}}{{{r},{g},{b}}}\\fill[c] ({bx + i * 0.06:.3f},{by:.3f}) rectangle ({bx + (i + 1) * 0.06 + 0.002:.3f},{by + 0.18:.3f});")
for e in range(0, 8):
    out.append(f"\\node[anchor=south] at ({bx + e * 0.6:.3f},{by + 0.18:.3f}) {{$10^{{{e}}}$}};")
out.append(f"\\node[anchor=west] at ({bx + 76 * 0.06 + 0.25:.3f},{by + 0.09:.3f}) {{\\small nodes at depth $j$}};")
out.append("\\end{tikzpicture}")
open("fig_profile.tex", "w").write("\n".join(out) + "\n")
