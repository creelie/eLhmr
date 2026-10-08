#!/usr/bin/env python3
"""
Lehmer's equation n - 1 = 2 phi(n) with k = 15 prime factors and p_1 >= 5.

The 54,985 nodes at depth 12 (data/k15/frontier.json, recomputed here and checked against the file) give the
interval for p_13.  For every admissible prime s = p_13 in it, lastthree.two_prime_completions finds all
integers p < q with n = A s p q satisfying the equation, through the divisors of
N = 2 A' B' - C' in the class -2B' (mod C').  Work is split into tasks (a prefix, or a piece of the interval of
a long prefix), run on several cores, and every finished task is appended to a JSON-lines log, so an
interrupted run resumes where it stopped.

With --program B the same tasks are done by the independent implementation lastthree_b.py (its own
frontier from Program 1's rational bounds, its own prime generation, a different lattice-point method and a
different factoring threshold).  With --program C they are done by lastthree_c.py, which uses neither lattice
boxes nor factoring: the two factors t <= t* of N lie in the same class modulo C', so their sum is fixed modulo
C'^2 and is found by a short scan with one square test per value.  With --eps +1 the equation is n + 1 = 2 phi(n) (the companion equation with
3 not dividing n); its frontier at depth 12 is the same.

usage: k15_run.py OUT.jsonl [--program A|B|C] [--eps -1|1] [--workers 4] [--hours H] [--kappa K]
                  [--max-boxes M] [--split S]
"""
import sys, os, json, time, argparse, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lastthree as L
import lastthree_b as LB
import lastthree_c as LC

K, PMIN, A_, B_ = 15, 5, 2, 1

def prefix_AB(chosen):
    A = 1; B = 1
    for p in chosen: A *= p; B *= p - 1
    return A, B

def tasks(frontier, split):
    out = []
    for i, (chosen, lo, hi) in enumerate(frontier):
        a = lo
        while a <= hi:
            b = min(hi, a + split - 1)
            out.append((i, a, b)); a = b + 1
    return out

def cost_key(task, frontier):
    i, a, b = task
    chosen, lo, hi = frontier[i]
    # the work is concentrated just above the lower end of long intervals
    return -((hi - lo + 1) ** 2 / (a - lo + 1 + (hi - lo + 1) / 100.0)) * ((b - a + 1) / (hi - lo + 1))

G = {}
def init(frontier, kappa, max_boxes, program, eps):
    G['fr'] = frontier; G['kappa'] = kappa; G['mb'] = max_boxes; G['prog'] = program; G['eps'] = eps

def work(task):
    i, a, b = task
    chosen, lo, hi = G['fr'][i]
    chosen = tuple(chosen)
    A, B = prefix_AB(chosen)
    t0 = time.time(); eps = G['eps']
    if G['prog'] == 'C':
        st = LC.StatsC(); cands = []
        n_s, sols = LC.node_c(chosen, A, B, a, b, A_, B_, eps, stats=st, cands=cands)
        return {"task": [i, a, b], "n_s": n_s, "tested": st.sums, "direct": st.direct, "found": st.found,
                "cands": cands, "sols": sols, "sec": round(time.time() - t0, 3)}
    if G['prog'] == 'B':
        st = LB.StatsB(); cands = []
        n_s, sols = LB.node_b(chosen, A, B, a, b, A_, B_, eps, stats=st, cands=cands, max_boxes=G['mb'])
        return {"task": [i, a, b], "n_s": n_s, "boxes": st.boxes, "tested": st.points,
                "factored": st.factored, "found": st.found, "cands": cands, "sols": sols,
                "sec": round(time.time() - t0, 3)}
    ss = L.primes_in(a, b)
    ss = ss[L.admissible_mask(ss, chosen)]
    st = L.Stats(); cands = []; sols = []
    for s in ss.tolist():
        sols += L.two_prime_completions(chosen + (s,), A * s, B * (s - 1), A_, B_, eps, stats=st,
                                        max_boxes=G['mb'], cands=cands, kappa=G['kappa'])
    return {"task": [i, a, b], "n_s": len(ss), "boxes": st.boxes, "tested": st.hits, "direct": st.direct,
            "factored": st.factored, "found": st.found, "cands": cands, "sols": sols,
            "sec": round(time.time() - t0, 3)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out"); ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--hours", type=float, default=1.9); ap.add_argument("--kappa", type=float, default=1.0)
    ap.add_argument("--max-boxes", type=int, default=None); ap.add_argument("--split", type=int, default=1_000_000)
    ap.add_argument("--program", choices=["A", "B", "C"], default="A"); ap.add_argument("--eps", type=int, default=-1)
    args = ap.parse_args()
    if args.max_boxes is None: args.max_boxes = 50000 if args.program == "A" else 5000
    fr_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "k15", "frontier.json")
    frontier = json.load(open(fr_path))
    if args.program in ("A", "C"):
        check = [[list(c), lo, hi] for c, A, B, lo, hi in L.frontier(K, PMIN, A_, B_, args.eps, 3)]
        assert check == frontier, "frontier.json does not match the recomputed frontier"
    else:
        check = {(tuple(c), lo, hi) for c, A, B, lo, hi in LB.frontier_rational(K, PMIN, A_, B_, args.eps, 3)}
        assert check == {(tuple(c), lo, hi) for c, lo, hi in frontier}, "frontier mismatch (rational bounds)"
    T = tasks(frontier, args.split)
    done = set()
    if os.path.exists(args.out):
        for line in open(args.out):
            try: done.add(tuple(json.loads(line)["task"]))
            except Exception: pass
    todo = [t for t in T if t not in done]
    todo.sort(key=lambda t: cost_key(t, frontier))
    print(f"program {args.program}, eps={args.eps:+d}: {len(T)} tasks, {len(done)} done, {len(todo)} to do; "
          f"kappa={args.kappa}, max_boxes={args.max_boxes}", flush=True)
    t_end = time.time() + 3600 * args.hours; t0 = time.time()
    n = 0; ns = 0; nsol = 0
    with open(args.out, "a") as f, mp.Pool(args.workers, initializer=init,
                                           initargs=(frontier, args.kappa, args.max_boxes, args.program, args.eps)) as pool:
        for res in pool.imap_unordered(work, todo, chunksize=1 if len(todo) < 5000 else 8):
            f.write(json.dumps(res) + "\n"); f.flush()
            n += 1; ns += res["n_s"]; nsol += len(res["sols"])
            if res["sols"]: print("SOLUTION", res, flush=True)
            if n % 2000 == 0 or res["sec"] > 600:
                print(f"{n}/{len(todo)} tasks, {ns} values of p_13, {nsol} solutions, "
                      f"{time.time()-t0:.0f}s", flush=True)
            if time.time() > t_end:
                print("time limit reached; rerun to resume", flush=True)
                pool.terminate(); break
    print(f"finished this session: {n} tasks, {ns} values of p_13, {nsol} solutions, {time.time()-t0:.0f}s",
          flush=True)

if __name__ == "__main__":
    main()
