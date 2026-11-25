#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Inventory of the displayed derivations of Williams's TOCT paper, Section 7 (pp. A:31-A:38), against the
rules of the formal calculus HY.Step.

Every displayed transition is replayed at exact rational parameter values that satisfy the side conditions
Williams states: the rule is applied (Lemma 7.1 merged or opening a block, Lemma 3.3 merged into the
innermost block, Lemma 7.2), and its output is compared component by component with the printed line, once
from the printed previous line and once from the line HY.Step produced. A printed superscript that is
omitted is compared with Williams's default (p. A:5) read block-wise: max{guess, 1}. The new log n block of
Lemma 3.3 is given the output l(o, e) for four functions l: max(o, e) (HY.Step), 1, max(o, 1) and
max(1, e) (HY.StepO l). A Lemma 7.2 step is also evaluated with the maximum that the 0,1,0 display of
p. A:36 prints (without the output b_k of the remaining prefix).

The printed lines are transcribed from the rendered pages (the text layer loses superscripts and primes).
The 25-line proof of pp. A:32-A:33 is replayed separately by w13_25line.py. Corollary 7.8 (used twice in
the proof of Theorem 7.5) is a sub-derivation; it is constructed here from the rules (Lemma 7.1 merged,
Lemma 3.3 merged, Lemma 7.2, repeated) and its endpoint is compared with the displayed one.

Python 3 standard library only; exact arithmetic.

usage: inventory.py"""
import sys
from fractions import Fraction as Q

ELL = {
    "max": ("max(o,e)", lambda o, e: max(o, e)),
    "one": ("1", lambda o, e: Q(1)),
    "in": ("max(o,1)", lambda o, e: max(o, Q(1))),
    "sp": ("max(1,e)", lambda o, e: max(Q(1), e)),
}


def opp(q):
    return "A" if q == "E" else "E"


def pin(blocks):
    return blocks[-1][2] if blocks else Q(1)


class RuleError(Exception):
    pass


def conv(line, s, d, q="E"):
    blocks, ker = line
    if ker[0] != "T":
        raise RuleError("Lemma 7.1 needs a DTIME_d kernel")
    a = ker[1]
    if not (0 < s <= a and pin(blocks) >= 1):
        raise RuleError("Lemma 7.1 side condition")
    if blocks and blocks[-1][0] == q:
        bq, g, o = blocks[-1]
        nb = blocks[:-1] + [(bq, max(g, a - s), max(a - s, o))]
    else:
        nb = blocks + [(q, a - s, max(a - s, pin(blocks)))]
    return nb, ("S", a, d * s)


def speed(line, x, ell="max"):
    blocks, ker = line
    if ker[0] != "S" or not blocks:
        raise RuleError("Lemma 3.3 in a prefix needs a DTISP kernel under a block")
    a, e = ker[1], ker[2]
    q, g, o = blocks[-1]
    if not (a >= 1 and 0 <= e <= a - x and 0 <= x <= a - 1 and o >= 1):
        raise RuleError("Lemma 3.3 side condition")
    nb = blocks[:-1] + [(q, max(g, x + e), max(o, x + e)), (opp(q), Q(0), ELL[ell][1](o, e))]
    return nb, ("S", a - x, e)


def slow(line, c, omit_bk=False):
    blocks, ker = line
    if not blocks:
        raise RuleError("Lemma 7.2 needs a block")
    q, g, o = blocks[-1]
    bk = pin(blocks[:-1])
    if not (bk >= 1 and o >= 1 and ker[1] >= 1 and g >= 0):
        raise RuleError("Lemma 7.2 side condition")
    m = max(o, g, ker[1]) if omit_bk else max(bk, o, g, ker[1])
    return blocks[:-1], ("T", c * m)


def cor78(line, c, d, ell="max"):
    """Corollary 7.8 inside a prefix whose innermost block has output G = guess G: from (.., T G*A') with
    1 <= A' < eta, Lemma 7.7's rounds (Lemma 7.1 merged with s = G(A'-1), Lemma 3.3 merged so that the raised
    guess stays G, Lemma 7.2) until A' <= e_1, then the base case (s = G/(d+1), x = G(A'-1)). Returns the
    endpoint and the number of steps."""
    blocks, ker = line
    G = pin(blocks)
    e1 = Q(d + 2, d + 1)
    steps = 0
    while True:
        A1 = line[1][1] / G
        q = line[0][-1][0]
        if A1 <= e1:
            line = conv(line, G / (d + 1), d, q)
            line = speed(line, G * (A1 - 1), ell)
            return line, steps + 2
        A = c * (d + 1) * (A1 - 1)
        line = conv(line, G * (A1 - 1), d, q)
        line = speed(line, G * (A1 - A / c), ell)
        line = slow(line, c)
        steps += 3


def show_num(x):
    return f"{float(x):.6g}"


def show(line):
    blocks, ker = line
    bs = []
    for q, g, o in blocks:
        gs = "log" if g == 0 else "n^" + show_num(g)
        bs.append(f"({q} {gs})" + ("^" + show_num(o) if o is not None else ""))
    k = f"T[{show_num(ker[1])}]" if ker[0] == "T" else f"S[{show_num(ker[1])},{show_num(ker[2])}]"
    return " ".join(bs + [k])


def compare(ours, printed):
    """Differences between a computed line and a printed one (printed output None = omitted)."""
    out = []
    ob, ok = ours
    pb, pk = printed
    if [q for q, *_ in ob] != [q for q, *_ in pb]:
        return [f"blocks {[q for q, *_ in ob]} vs printed {[q for q, *_ in pb]}"]
    for i, ((q, g, o), (_, pg, po)) in enumerate(zip(ob, pb)):
        if g != pg:
            out.append(f"guess of block {i + 1}: ours {show_num(g)}, printed {show_num(pg)}")
        if po is None:
            dflt = max(pg, Q(1))
            if o != dflt:
                out.append(f"output of block {i + 1}: ours {show_num(o)}, omitted (block-wise default "
                           f"{show_num(dflt)})")
        elif o != po:
            out.append(f"output of block {i + 1}: ours {show_num(o)}, printed {show_num(po)}")
    if ok[0] != pk[0]:
        out.append(f"kernel: ours {'DTIME' if ok[0] == 'T' else 'DTISP'}, printed {'DTIME' if pk[0] == 'T' else 'DTISP'}")
    else:
        for name, x, y in zip(("time", "space"), ok[1:], pk[1:]):
            if x != y:
                out.append(f"{name}: ours {show_num(x)}, printed {show_num(y)}")
    return out


def fill(line):
    """A printed line with every omitted output superscript replaced by the block-wise default max{guess, 1}."""
    blocks, ker = line
    return [(q, g, max(g, Q(1)) if o is None else o) for q, g, o in blocks], ker


SUMMARY = []


def run(title, start, trans, c, d, ell="max"):
    """trans: list of (label, rule function line->line, printed line). Prints a row per transition with the
    differences from the printed previous line and from our previous line."""
    print(f"\n== {title} [l = {ELL[ell][0]}]")
    print(f"   start (printed): {show(start)}")
    ours = fill(start)
    prev_printed = start
    rows = []
    for label, rule, printed in trans:
        try:
            from_p = rule(fill(prev_printed))
            dp = compare(from_p, printed)
        except RuleError as err:
            dp = [f"rule not applicable to the printed line ({err})"]
        try:
            ours = rule(ours)
            do = compare(ours, printed)
        except RuleError as err:
            do = [f"rule not applicable ({err})"]
        print(f"   {label}")
        print(f"     printed: {show(printed)}")
        print(f"     ours:    {show(ours)}")
        print("     from printed previous line: " + ("agrees" if not dp else "; ".join(dp)))
        print("     from our previous line:     " + ("agrees" if not do else "; ".join(do)))
        rows.append((label, dp))
        prev_printed = printed
    SUMMARY.append((title, ell, rows))
    return ours


def P(blocks, ker):
    return ([tuple(b) for b in blocks], ker)


def example_a31():
    c, d = Q(6, 5), 1
    L0 = P([], ("T", Q(3, 2)))
    run("p. A:31, Example (Kannan, van Melkebeek-Raz), d = 1, c = 6/5", L0, [
        ("Lemma 7.1, s = 1/2", lambda L: conv(L, Q(1, 2), d),
         P([("E", Q(1), None)], ("S", Q(3, 2), Q(1, 2)))),
        ("Lemma 3.3, x = 1/2", lambda L: speed(L, Q(1, 2)),
         P([("E", Q(1), None), ("A", Q(0), None)], ("S", Q(1), Q(1, 2)))),
        ("Lemma 7.2", lambda L: slow(L, c), P([("E", Q(1), None)], ("T", c))),
        ("Lemma 7.2", lambda L: slow(L, c), P([], ("T", c * c))),
    ], c, d)


def lemma77():
    for d in (1, 2):
        c = Q(129, 100) if d == 1 else Q(118, 100)
        e = [None, Q(d + 2, d + 1)]
        for _ in range(3):
            e.append(1 + e[-1] / (c * (d + 1)))
        dd = Q(d, d + 1)
        run(f"p. A:33, Lemma 7.7 base case, d = {d}, c = {c}", P([], ("T", e[1])), [
            ("Lemma 7.1, s = 1/(d+1)", lambda L: conv(L, Q(1, d + 1), d), P([("E", Q(1), None)], ("S", e[1], dd))),
            ("Lemma 3.3, x = 1/(d+1)", lambda L: speed(L, Q(1, d + 1)),
             P([("E", Q(1), None), ("A", Q(0), None)], ("S", Q(1), dd))),
        ], c, d)
        k = 2
        a = 1 + e[k] / (c * (d + 1))
        s = e[k] / (c * (d + 1))
        run(f"p. A:33, Lemma 7.7 inductive step, k = {k}, d = {d}, c = {c}", P([], ("T", a)), [
            ("Lemma 7.1, s = e_k/(c(d+1))", lambda L: conv(L, s, d), P([("E", Q(1), None)], ("S", a, d * s))),
            ("Lemma 3.3, x = 1 + e_k/(c(d+1)) - e_k/c", lambda L: speed(L, a - e[k] / c),
             P([("E", Q(1), None), ("A", Q(0), None)], ("S", e[k] / c, d * s))),
            ("Lemma 7.2", lambda L: slow(L, c), P([("E", Q(1), None)], ("T", e[k]))),
        ], c, d)


def theorem75():
    d, c = 1, Q(129, 100)
    a, x = Q(44, 25), Q(13, 50)
    G = x + d * (a - 1)
    eta = c * (d + 1) / (c * (d + 1) - 1)
    es = c * ((d + 1) * (a - 1) - x)
    t1 = 1 - d * (a - 1)
    print(f"\n   Theorem 7.5 parameters: d = {d}, c = {c}, a = {a}, x = {x}; x + d(a-1) = {G}, "
          f"1 - d(a-1) = {t1}, e* = c((d+1)(a-1) - x) = {es} < eta = {eta}: {es < eta}, "
          f"c^2/(x+d(a-1)) = {c * c / G} < eta: {c * c / G < eta}, final c^2(x+d(a-1)) = {c * c * G} < a: {c * c * G < a}")
    for ell in ("max", "one"):
        Ln = run(f"p. A:34, proof of Theorem 7.5, d = {d}, c = {c}", P([], ("T", a)), [
            ("Lemma 7.1, s = a-1", lambda L: conv(L, a - 1, d), P([("E", Q(1), None)], ("S", a, d * (a - 1)))),
            ("Lemma 3.3 (Speedup), x", lambda L: speed(L, x, ell),
             P([("E", G, G), ("A", Q(0), Q(1))], ("S", a - x, d * (a - 1)))),
            ("Lemma 3.3 (Speedup), x' = 1-d(a-1)", lambda L: speed(L, t1, ell),
             P([("E", G, G), ("A", t1 + d * (a - 1), Q(1)), ("E", Q(0), Q(1))], ("S", a - x - t1, d * (a - 1)))),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c),
             P([("E", G, G), ("A", Q(1), Q(1))], ("T", c * (a - x - t1)))),
            ("Corollary 7.8 (sub-derivation)", lambda L: cor78(L, c, d, ell)[0],
             P([("E", G, None), ("A", Q(1), None), ("E", Q(0), None)], ("S", Q(1), Q(d, d + 1)))),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c),
             P([("E", G, None), ("A", Q(1), None)], ("S", c, Q(d, d + 1)))),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([("E", G, G)], ("T", c * c))),
            ("Corollary 7.8 at scale x+d(a-1) (sub-derivation)", lambda L: cor78(L, c, d, ell)[0],
             P([("E", G, None), ("A", Q(1), None)], ("S", G, G * Q(d, d + 1)))),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([("E", G, None)], ("T", c * G))),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([], ("T", c * c * G))),
        ], c, d, ell)
        print(f"   final exponent {Ln[1][1]} = {float(Ln[1][1]):.6f} < a = {a}: {Ln[1][1] < a}")
    n1 = cor78(([("E", G, G), ("A", Q(1), Q(1))], ("T", es)), c, d)[1]
    n2 = cor78(([("E", G, G)], ("T", c * c)), c, d)[1]
    print(f"   the two Corollary 7.8 sub-derivations have {n1} and {n2} steps")
    bad = []
    for k in range(1, 400):
        A1 = 1 + (eta - 1) * Q(k, 400)
        try:
            end = cor78(([("A", Q(1), Q(1))], ("T", A1)), c, d)[0]
            if end != ([("A", Q(1), Q(1)), ("E", Q(0), Q(1))], ("S", Q(1), Q(d, d + 1))):
                bad.append(A1)
        except RuleError:
            bad.append(A1)
    print(f"   Corollary 7.8 endpoint (A n)^1 (E log)^1 DTISP[n, n^(d/(d+1))] reached exactly from DTIME_d[n^A'] "
          f"for A' = 1 + (eta-1)k/400, k = 1..399: {'all' if not bad else 'fails at ' + str(bad[:3])}")


def thm79_1100():
    for d, c, a, x, y in ((1, Q(3, 2), Q(4), Q(1), Q(1)), (1, Q(3, 2), Q(3), Q(1, 2), Q(2)),
                          (2, Q(4, 3), Q(5), Q(2), Q(1, 2))):
        m = max(a - x, y + d * x, Q(1), a - y)
        for ell in ELL:
            run(f"p. A:36, Theorem 7.9, annotation [1,1,0,0], d = {d}, c = {c}, a = {a}, x = {x}, y = {y}",
                P([], ("T", a)), [
                    ("Lemma 7.1, s = x", lambda L: conv(L, x, d),
                     P([("E", a - x, max(a - x, Q(1)))], ("S", a, d * x))),
                    ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                     P([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))],
                       ("S", a - y, d * x))),
                    ("Lemma 7.2", lambda L: slow(L, c),
                     P([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1)))], ("T", c * m))),
                    ("Lemma 7.2", lambda L: slow(L, c), P([], ("T", c * c * m))),
                ], c, d, ell)


def thm79_010():
    print("\n   The 0,1,0 display of p. A:36 (Lemma 7.2 maximum printed without b'):")
    for d, c, bp, ap, b, a, s in ((1, Q(3, 2), Q(10), Q(5), Q(5), Q(15, 2), Q(15, 4)),
                                   (1, Q(3, 2), Q(2), Q(3), Q(3), Q(4), Q(1))):
        start = P([("A", Q(0), bp), ("E", ap, b)], ("T", a))
        run(f"p. A:36, 0,1,0, d = {d}, c = {c}, b' = {bp}, a' = {ap}, b = {b}, a = {a}, s = {s}", start, [
            ("Lemma 7.1 (merged), s", lambda L: conv(L, s, d),
             P([("A", Q(0), bp), ("E", max(ap, a - s), max(b, a - s))], ("S", a, d * s))),
            ("Lemma 7.2", lambda L: slow(L, c),
             P([("A", Q(0), bp)], ("T", max(c * b, c * a - c * s, c * ap, c * a, c * d * s)))),
        ], c, d)
        L1 = conv(start, s, d)
        print(f"     Lemma 7.2 with the printed maximum (without b'): {show(slow(L1, c, omit_bk=True))}")
        run(f"p. A:36, 0,0 comparison, same parameters", start, [
            ("Lemma 7.2", lambda L: slow(L, c), P([("A", Q(0), bp)], ("T", max(c * b, c * a, c * ap)))),
        ], c, d)


def thm79_case1():
    for d, c, b, ap, a, e, x, y in ((1, Q(3, 2), Q(2), Q(1), Q(8), Q(3), Q(1), Q(1)),
                                    (1, Q(3, 2), Q(4), Q(2), Q(8), Q(1), Q(2), Q(1)),
                                    (1, Q(3, 2), Q(2), Q(2), Q(6), Q(1, 2), Q(3), Q(1, 2))):
        for ell in ELL:
            start = P([("A", Q(0), b), ("E", ap, b)], ("S", a, e))
            m3 = max(b, y + e, Q(1), a - x - y)
            run(f"p. A:37, Case 1, d = {d}, c = {c}, b = {b}, a' = {ap}, a = {a}, e = {e}, x = {x}, y = {y}",
                start, [
                    ("Lemma 3.3, x", lambda L: speed(L, x, ell),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", Q(0), max(b, Q(1)))],
                       ("S", a - x, e))),
                    ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", y, max(b, y + e, Q(1))),
                        ("E", Q(0), max(b, Q(1)))], ("S", a - x - y, e))),
                    ("Lemma 7.2", lambda L: slow(L, c),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", y, max(b, y + e, Q(1)))],
                       ("T", c * m3))),
                    ("Lemma 7.2", lambda L: slow(L, c),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e))],
                       ("T", c * c * max(b, y + e, Q(1), x + e, a - x - y)))),
                ], c, d, ell)
            run("p. A:37, Case 1, the string 1,0, same parameters", start, [
                ("Lemma 3.3, x", lambda L: speed(L, x, ell),
                 P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", Q(0), max(b, Q(1)))],
                   ("S", a - x, e))),
                ("Lemma 7.2", lambda L: slow(L, c),
                 P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e))],
                   ("T", c * max(b, Q(1), x + e, a - x)))),
            ], c, d, ell)


def thm79_case2():
    for d, c, b, ap, a, x, y in ((1, Q(3, 2), Q(2), Q(1), Q(6), Q(2), Q(1)),
                                 (1, Q(3, 2), Q(1), Q(5), Q(4), Q(1), Q(1, 2))):
        for ell in ELL:
            start = P([("A", Q(0), b), ("E", ap, b)], ("T", a))
            m = max(a - x, y + d * x, b, a - y)
            run(f"p. A:38, Case 2, d = {d}, c = {c}, b = {b}, a' = {ap}, a = {a}, x = {x}, y = {y}", start, [
                ("Lemma 7.1 (merged), s = x", lambda L: conv(L, x, d),
                 P([("A", Q(0), b), ("E", max(ap, a - x), max(b, a - x))], ("S", a, d * x))),
                ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                 P([("A", Q(0), b), ("E", max(ap, a - x, y + d * x), max(a - x, y + d * x, b)), ("A", Q(0), Q(1))],
                   ("S", a - y, d * x))),
                ("Lemma 7.2", lambda L: slow(L, c),
                 P([("A", Q(0), b), ("E", max(ap, a - x, y + d * x), max(a - x, y + d * x, b))], ("T", c * m))),
                ("Lemma 7.2", lambda L: slow(L, c),
                 P([("A", Q(0), b)], ("T", c * c * max(ap, a - x, y + d * x, b, a - y)))),
            ], c, d, ell)
            run("p. A:38, Case 2, the string 0 (inline: c max{a, a', b}), same parameters", start, [
                ("Lemma 7.2", lambda L: slow(L, c), P([("A", Q(0), b)], ("T", c * max(a, ap, b)))),
            ], c, d, ell)


def main():
    example_a31()
    lemma77()
    theorem75()
    thm79_1100()
    thm79_010()
    thm79_case1()
    thm79_case2()
    print("\n== Summary: transitions whose output differs from the printed line, the rule applied to the printed"
          " previous line (omitted superscripts read block-wise)")
    for title, ell, rows in SUMMARY:
        bad = [f"{label}: {'; '.join(dp)}" for label, dp in rows if dp]
        print(f"   {title} [l = {ELL[ell][0]}]: " + ("all agree" if not bad else " | ".join(bad)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
