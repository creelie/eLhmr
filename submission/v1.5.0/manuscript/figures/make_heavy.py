"""Writes fig_margins.tex and fig_trees.tex (Section 6 of the paper) from the search records in bound/logs."""
import json, os
here = os.path.dirname(os.path.abspath(__file__))
logs = os.path.join(here, '..', '..', 'bound', 'logs')

# fig_margins: per depth, the range of log2 log2 A_j and of log2 log2 V_j(mu) over the nodes of T_7
prof = json.load(open(os.path.join(logs, 'prof_s7.json')))
bars = []
for j in range(6, 14):
    bars.append(r'\draw[line width=1.3pt, orange!55!white] (axis cs:%.2f,%d) -- (axis cs:%.2f,%d);' % (j + 0.01, j - 6, j + 0.31, j - 6))
for j in range(7, 14):
    bars.append(r'\draw[line width=1.3pt, blue!40!white] (axis cs:%.2f,%d) -- (axis cs:%.2f,%d);' % (j - 0.31, j - 7, j - 0.01, j - 7))
for j, v in sorted(prof.items(), key=lambda t: int(t[0])):
    j = int(j)
    lo, hi = v['lv']
    bars.append(r'\draw[vbar] (axis cs:%.2f,%.6f) -- (axis cs:%.2f,%.6f);' % (j + 0.13, lo, j + 0.13, max(hi, lo + 0.04)))
    if v['lp'] is not None:
        lo, hi = v['lp']
        bars.append(r'\draw[pbar] (axis cs:%.2f,%.6f) -- (axis cs:%.2f,%.6f);' % (j - 0.13, lo, j - 0.13, max(hi, lo + 0.04)))
tex = r'''\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=0.56\textwidth,
  xmin=-0.6, xmax=13.7, ymin=0, ymax=7.9, xtick={0,1,...,13}, ytick={0,1,...,7},
  tick label style={font=\scriptsize}, label style={font=\small},
  xlabel={depth $j$}, ylabel={$\log_2\log_2$},
  grid=major, grid style={black!7}, axis line style={black!45},
  clip=false,
  legend style={at={(0.02,0.98)}, anchor=north west, draw=black!25, fill=white, font=\small, row sep=1pt},
  legend cell align=left]
\addlegendimage{line width=3.2pt, orange!80!black}
\addlegendentry{$V_j(\mu)$ over the nodes}
\addlegendimage{line width=3.2pt, blue!65!black}
\addlegendentry{$A_j$ over the nodes}
\addlegendimage{line width=1.3pt, orange!55!white}
\addlegendentry{threshold of (H2): $j+1-7$}
\addlegendimage{line width=1.3pt, blue!40!white}
\addlegendentry{threshold of (H1): $j-7$}
\tikzset{vbar/.style={line width=3.2pt, orange!80!black, line cap=round},
         pbar/.style={line width=3.2pt, blue!65!black, line cap=round}}
''' + '\n'.join(bars) + r'''
\end{axis}
\end{tikzpicture}
'''
open(os.path.join(here, 'fig_margins.tex'), 'w').write(tex)

# fig_trees: nodes per depth for s = 4..7 on a log scale
styles = {4: 'teal!70!black, mark=square*', 5: 'blue!65!black, mark=triangle*',
          6: 'violet!75!black, mark=diamond*', 7: 'orange!85!black, mark=*'}
plots = []
for s in (4, 5, 6, 7):
    h = json.load(open(os.path.join(logs, 'hist_s%d.json' % s)))
    coords = ' '.join('(%d,%d)' % (j, c) for j, c in h['by_depth'])
    plots.append(r'\addplot[thick, %s, mark size=1.9pt] coordinates {%s};' % (styles[s], coords))
    plots.append(r'\addlegendentry{$s=%d$ \ (%s nodes)}' % (s, str(h['nodes'])))
tex = r'''\begin{tikzpicture}
\begin{semilogyaxis}[width=0.86\textwidth, height=0.52\textwidth,
  xmin=-0.4, xmax=13.4, ymin=0.7, ymax=60000, xtick={0,1,...,13},
  ytick={1,10,100,1000,10000}, yticklabels={$1$,$10$,$10^2$,$10^3$,$10^4$},
  tick label style={font=\scriptsize}, label style={font=\small},
  xlabel={depth $j$}, ylabel={nodes of $\mathcal T_s$ at depth $j$},
  grid=major, grid style={black!7}, axis line style={black!45},
  legend style={at={(0.02,0.98)}, anchor=north west, draw=black!25, fill=white, font=\small},
  legend cell align=left]
''' + '\n'.join(plots) + r'''
\end{semilogyaxis}
\end{tikzpicture}
'''
open(os.path.join(here, 'fig_trees.tex'), 'w').write(tex)
print('fig_margins.tex fig_trees.tex')
