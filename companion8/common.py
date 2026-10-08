"""Shared helpers for the programs in this directory: running scan3 and the PARI/GP factoring pass."""
import os, subprocess, tempfile
from math import prod

HERE = os.path.dirname(os.path.abspath(__file__))
SCAN3 = os.path.join(HERE, "scan3")
GPSCRIPT = os.path.join(HERE, "factor_class.gp")


def build():
    """compile scan3 if needed."""
    src = os.path.join(HERE, "scan3.c")
    if not os.path.exists(SCAN3) or os.path.getmtime(SCAN3) < os.path.getmtime(src):
        subprocess.run(["gcc", "-O3", "-march=native", "-o", SCAN3, src, "-lgmp", "-lm"], check=True)


def line0(eps, prefix, lo, hi):
    """input line for scan3, mode 0 (prime entries)."""
    return f"{eps} 0 {len(prefix)} {' '.join(map(str, prefix))} {lo} {hi}"


def run_scan3(lines, params=()):
    """run scan3 on the given input lines; returns (totals, completions, deferred).
    totals: dict of summed T fields; completions: list of tuples (x_1, .., x_j, x, p, q); deferred: list of tuples
    (x_1, .., x_j, x)."""
    p = subprocess.run([SCAN3] + [str(a) for a in params], input="\n".join(lines) + "\n",
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"scan3 failed: {p.stderr[:500]}")
    keys = ("nx", "nempty", "ntd", "nsig", "nsurv", "nfound", "ndef", "sec")
    tot = dict.fromkeys(keys, 0.0); tot["tasks"] = 0
    comps, defs = [], []
    for l in p.stdout.splitlines():
        v = l.split()
        if v[0] == "T":
            tot["tasks"] += 1
            for k, x in zip(keys, v[1:]): tot[k] += float(x)
        elif v[0] == "S":
            comps.append(tuple(int(x) for x in v[1:]))
        elif v[0] == "F":
            defs.append(tuple(int(x) for x in v[1:]))
    if tot["tasks"] != len(lines):
        raise RuntimeError(f"scan3 returned {tot['tasks']} of {len(lines)} tasks: {p.stderr[:500]}")
    return tot, comps, defs


def run_gp(tuples, eps, tmpdir=None):
    """factor N for each tuple (x_1, .., x_j, x) with PARI/GP (every prime factor proved prime) and return
    (list of completions (x_1, .., x, p, q, isprime(p), isprime(q)), largest number of digits of N, seconds)."""
    if not tuples:
        return [], 0, 0.0
    fd, path = tempfile.mkstemp(suffix=".gp", dir=tmpdir)
    with os.fdopen(fd, "w") as f:
        for t in tuples: f.write("[" + ",".join(map(str, t)) + "]\n")
    head = f'IN="{path}"; EPS={eps};\n'
    script = head + open(GPSCRIPT).read()
    p = subprocess.run(["gp", "-q", "-s", "400000000", "--default", "nbthreads=1"], input=script,
                       capture_output=True, text=True)
    os.unlink(path)
    comps = []; G = None
    for l in p.stdout.splitlines():
        v = l.split()
        if not v: continue
        if v[0] == "C": comps.append(tuple(int(x) for x in v[1:]))
        elif v[0] == "G": G = v[1:]
    if G is None or int(G[0]) != len(tuples):
        raise RuntimeError(f"gp failed: {p.stdout[-500:]} {p.stderr[-500:]}")
    return comps, int(G[2]), float(G[3])


def check_completion(t, eps):
    """exact check of A x p q + eps = 2 B (x-1)(p-1)(q-1) for the tuple t = (x_1, .., x_k)."""
    return prod(t) + eps == 2 * prod(x - 1 for x in t) and all(a < b for a, b in zip(t, t[1:]))


SMALL = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)


def sifted(c):
    """the conditions that prime entries p, q (the last two of the completion c) satisfy and that the filters of
    scan3 use: no prime factor up to 61 other than themselves, p, q != 1 modulo the earlier entries, and
    p = q = 2 mod 3 if 3 is an entry.  Every route of scan3 and the factoring pass find every completion with this
    property; completions without it may be dropped by the filters of one route and reported by another."""
    *pre, p, q = c
    return all(y % l or y == l for y in (p, q) for l in SMALL) and all(y % z != 1 for y in (p, q) for z in pre) and \
        (3 not in pre or (p % 3 == 2 and q % 3 == 2))
