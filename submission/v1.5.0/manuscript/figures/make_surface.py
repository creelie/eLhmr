import math, os
# Writes fig_surface.tex: the surface of the last three entries s < p < q, on which
# s/(s-1) * p/(p-1) * q/(q-1) = tau, drawn for tau = 1.1 on logarithmic axes, with three slices s = const.
tau = 1.1
f = lambda x: x / (x - 1)
finv = lambda w: w / (w - 1)
s_lo, s_hi = 11.8, finv(tau ** (1 / 3))


def p_range(s):
    g = tau / f(s)
    return max(s, 1.12 * finv(g)), finv(math.sqrt(g))


def q_of(s, p):
    return finv(tau / (f(s) * f(p)))


def point(s, p):
    return '(%.5g,%.5g,%.5g)' % (s, p, q_of(s, p))


U, V = 36, 24
rows = []
for i in range(U + 1):
    s = math.exp(math.log(s_lo) + (math.log(s_hi - 0.08) - math.log(s_lo)) * i / U)
    a, b = p_range(s)
    rows.append(' '.join(point(s, math.exp(math.log(a) + (math.log(b) - math.log(a)) * j / V)) for j in range(V + 1)))


def slice_curve(s, n=40):
    a, b = p_range(s)
    return ' '.join(point(s, math.exp(math.log(a) + (math.log(b) - math.log(a)) * j / n)) for j in range(n + 1))


diag = ' '.join('(%.5g,%.5g,%.5g)' % (s, p_range(s)[1], p_range(s)[1])
                for s in [math.exp(math.log(s_lo) + (math.log(s_hi) - math.log(s_lo)) * i / 60) for i in range(61)])

tex = r'''\begin{tikzpicture}
\begin{axis}[width=0.9\textwidth, height=0.66\textwidth, view={128}{24},
  xmode=log, ymode=log, zmode=log, log basis x=10, log basis y=10, log basis z=10,
  xmin=11, xmax=34, ymin=14, ymax=280, zmin=28, zmax=1300,
  xtick={12,16,24,32}, xticklabels={$12$,$16$,$24$,$32$},
  ytick={16,32,64,128,256}, yticklabels={$16$,$32$,$64$,$128$,$256$},
  ztick={32,100,300,1000}, zticklabels={$32$,$100$,$300$,$1000$},
  tick label style={font=\scriptsize}, label style={font=\small},
  xlabel={$s$}, ylabel={$p$}, zlabel={$q$},
  grid=major, grid style={black!8}, axis line style={black!50},
  colormap={sheet}{rgb255=(214,230,244) rgb255=(120,170,214)}]
\addplot3[surf, shader=faceted interp, faceted color=black!18, line width=0.1pt, point meta=x, opacity=1] coordinates {
''' + '\n\n'.join(rows) + r'''
};
\addplot3[very thick, orange!85!black, smooth] coordinates {''' + slice_curve(13) + r'''};
\addplot3[very thick, orange!85!black, smooth] coordinates {''' + slice_curve(17) + r'''};
\addplot3[very thick, orange!85!black, smooth] coordinates {''' + slice_curve(23) + r'''};
\addplot3[thick, red!70!black, smooth] coordinates {''' + diag + r'''};
\node[font=\scriptsize, text=orange!60!black, anchor=south west] at (axis cs:13,%.4g,%.4g) {$s=13$};
\node[font=\scriptsize, text=orange!60!black, anchor=south west] at (axis cs:17,%.4g,%.4g) {$s=17$};
\node[font=\scriptsize, text=orange!60!black, anchor=south west] at (axis cs:23,%.4g,%.4g) {$s=23$};
\node[font=\scriptsize, text=red!60!black, anchor=north west] at (axis cs:%.4g,%.4g,%.4g) {$p=q$};
\end{axis}
\end{tikzpicture}
'''
lab = []
for s in (13, 17, 23):
    a, b = p_range(s)
    lab += [a, q_of(s, a)]
sd = 26.0
lab += [sd, p_range(sd)[1], p_range(sd)[1]]
tex = tex % tuple(lab)
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fig_surface.tex'), 'w').write(tex)
print('fig_surface.tex')
