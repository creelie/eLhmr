#!/usr/bin/env python3
"""Seeds for descent.py: every prefix of length 6 or more of the integer tree for k = 13 (integer_tree.py, eps = -1),
with its defect c = 2B - A. Writes prefixes_k13.pkl."""
import pickle
from integer_tree import depth_k3_nodes
nodes, visited = depth_k3_nodes(13, -1)
pre = {}
for xs, lo, hi in nodes:
    for d in range(6, len(xs) + 1):
        p = tuple(xs[:d])
        if p in pre: continue
        A = 1; B = 1
        for x in p: A *= x; B *= x - 1
        pre[p] = 2 * B - A
pickle.dump(pre, open('prefixes_k13.pkl', 'wb'))
print(len(pre), "prefixes")
