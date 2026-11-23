#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Recompute the k-line values of the TAUT table in W13 Section 6.2 by linear programming.

Exact rational arithmetic (Python standard library only; a small two-phase simplex with Bland's
rule). An annotation is a 0/1 sequence (1 = speedup, 0 = slowdown); the shapes of the lines, and
hence which form of Lemma 6.1 (new blocks or merged) and of Lemma 6.2 (pop or flip) applies, are
determined by it. For fixed c the proof exists iff an LP is feasible: every rule output is bounded
below by its exact value (W13 Section 6.1: "replace max{a,a'} = a'' with a'' >= a, a'' >= a'"),
Lemma 6.1's side conditions b >= 1, a >= 1, x >= 0 hold at each speedup, all values are >= 0, and
the last exponent is at most the first. Feasibility is monotone in c, so the best c of an
annotation is found by bisection.

The pop cost of Lemma 6.2(1),(2) is c * max(a_k, a_{k+1}, b_{k+1}, b); the option --no-b drops the
term b (the input constraint of the next outer block).

Usage: python3 w13_lp.py [--lines 5,8,11] [--no-b] [--digits 4] [--at 1.43308,1.43310]
Prints, for each number of lines, the valid annotations, the best c of each, and the maximum.
With --at, it instead decides feasibility exactly at each given c (a decimal, read as an exact
rational) and prints the annotations that are feasible there.
"""
import argparse
from fractions import Fraction as F


def feasible(rows, nvars):
    """rows: list of (dict var -> coefficient, rhs) meaning sum >= rhs; all variables >= 0."""
    m = len(rows)
    ncol = nvars + 2 * m
    tab = []
    for i, (co, rhs) in enumerate(rows):
        r = [F(0)] * (ncol + 1)
        for v, cf in co.items():
            r[v] += cf
        r[nvars + i] = F(-1)
        r[ncol] = F(rhs)
        if r[ncol] < 0:
            r = [-t for t in r]
        r[nvars + m + i] = F(1)
        tab.append(r)
    basis = [nvars + m + i for i in range(m)]
    obj = [sum(col) for col in zip(*tab)]
    for i in range(m):
        obj[nvars + m + i] = F(0)
    while obj[ncol] > 0:
        e = next((j for j in range(nvars + m) if obj[j] > 0), None)
        if e is None:
            return False
        best = None
        for i in range(m):
            if tab[i][e] > 0:
                ratio = tab[i][ncol] / tab[i][e]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                    best = (ratio, i)
        i = best[1]
        piv = tab[i][e]
        tab[i] = [t / piv for t in tab[i]]
        for k in range(m):
            if k != i and tab[k][e] != 0:
                f = tab[k][e]
                tab[k] = [a - f * b for a, b in zip(tab[k], tab[i])]
        f = obj[e]
        obj = [a - f * b for a, b in zip(obj, tab[i])]
        basis[i] = e
    return True


def shapes(ann):
    """Simulate the block structure. Returns the list of rules or None if the annotation is not a
    valid normal-form proof (no quantifier-free interior line, quantifier-free last line)."""
    blocks, kernel, rules = [], "E", []
    for t, step in enumerate(ann):
        if t > 0 and not blocks:
            return None
        if step == 1:
            if blocks and blocks[-1] == kernel:
                rules.append("merge")
                blocks = blocks + [("A" if kernel == "E" else "E")]
            else:
                rules.append("new")
                blocks = blocks + [kernel, ("A" if kernel == "E" else "E")]
        else:
            if not blocks:
                return None
            if blocks[-1] == kernel:
                rules.append("pop")
                blocks = blocks[:-1]
            else:
                rules.append("flip")
            kernel = "A" if kernel == "E" else "E"
    return rules if not blocks else None


def lp_rows(rules, c, with_b):
    """Variables: per block (guess, constraint) and per line the kernel exponent, plus x."""
    rows, nv = [], [0]

    def var():
        nv[0] += 1
        return nv[0] - 1

    one = None
    a0 = var()
    a = a0
    blocks = []  # list of (g, o) variable indices, outermost first

    def pin(bl):
        return bl[-1][1] if bl else one

    def ge(v, terms, rhs=0):
        co = {v: F(1)}
        for w, cf in terms:
            co[w] = co.get(w, F(0)) - cf
        rows.append((co, F(rhs)))

    for r in rules:
        if r in ("new", "merge"):
            x = var()
            a2 = var()
            rows.append(({a: F(1)}, F(1)))
            ge(a2, [(a, F(1)), (x, F(-1))])
            if r == "new":
                b = pin(blocks)
                if b is not None:
                    rows.append(({b: F(1)}, F(1)))
                g1, o1, g2, o2 = var(), var(), var(), var()
                ge(g1, [(x, F(1))])
                ge(o1, [(x, F(1))])
                if b is None:
                    rows.append(({o1: F(1)}, F(1)))
                    rows.append(({o2: F(1)}, F(1)))
                else:
                    ge(o1, [(b, F(1))])
                    ge(o2, [(b, F(1))])
                blocks = blocks + [(g1, o1), (g2, o2)]
            else:
                gu, ou = blocks[-1]
                rows.append(({ou: F(1)}, F(1)))
                g1, o1, g2, o2 = var(), var(), var(), var()
                ge(g1, [(gu, F(1))])
                ge(g1, [(x, F(1))])
                ge(o1, [(ou, F(1))])
                ge(o1, [(x, F(1))])
                ge(o2, [(ou, F(1))])
                blocks = blocks[:-1] + [(g1, o1), (g2, o2)]
            a = a2
        elif r == "flip":
            a2 = var()
            ge(a2, [(a, c)])
            ge(a2, [(blocks[-1][1], c)])
            a = a2
        else:
            a2 = var()
            gu, ou = blocks[-1]
            for w in (gu, a, ou):
                ge(a2, [(w, c)])
            if with_b:
                if len(blocks) >= 2:
                    ge(a2, [(blocks[-2][1], c)])
                else:
                    rows.append(({a2: F(1)}, c))
            blocks = blocks[:-1]
            a = a2
    rows.append(({a0: F(1), a: F(-1)}, F(0)))
    return rows, nv[0]


def best_c(rules, with_b, digits):
    lo, hi = F(1), F(2)
    if not feasible(*lp_rows(rules, lo, with_b)):
        return None
    eps = F(1, 10 ** digits)
    while hi - lo > eps:
        mid = (lo + hi) / 2
        if feasible(*lp_rows(rules, mid, with_b)):
            lo = mid
        else:
            hi = mid
    return lo, hi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lines", default="5,8,11")
    ap.add_argument("--no-b", action="store_true")
    ap.add_argument("--digits", type=int, default=4)
    ap.add_argument("--at", default=None)
    args = ap.parse_args()
    with_b = not args.no_b
    print("pop cost", "with" if with_b else "without", "the b term")
    for k in [int(s) for s in args.lines.split(",")]:
        n = k - 1
        valid = []
        for mask in range(2 ** n):
            ann = [(mask >> (n - 1 - i)) & 1 for i in range(n)]
            rules = shapes(ann)
            if rules is not None:
                valid.append((ann, rules))
        if args.at is not None:
            print(f"\n{k} lines: {len(valid)} valid annotations")
            for cs in args.at.split(","):
                c = F(cs)
                ok = [ann for ann, rules in valid if feasible(*lp_rows(rules, c, with_b))]
                print(f"  c = {cs}: {len(ok)} feasible annotation(s)")
                for ann in ok:
                    print(f"    {ann}")
            continue
        results = []
        for ann, rules in valid:
            bc = best_c(rules, with_b, args.digits)
            results.append((ann, bc))
        print(f"\n{k} lines: {len(results)} valid annotations")
        for ann, bc in results:
            s = "infeasible at c = 1" if bc is None else f"best c in [{float(bc[0]):.6f}, {float(bc[1]):.6f}]"
            print(f"  {ann}: {s}")
        vals = [bc[0] for _, bc in results if bc is not None]
        if vals:
            print(f"  maximum: {float(max(vals)):.6f}")


if __name__ == "__main__":
    main()
