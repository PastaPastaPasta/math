#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Inventory of the displayed derivations of Williams's TOCT paper, Section 7 (pp. A:31-A:38), against the
rules of the formal calculus HY.Step.

Every displayed transition below is replayed at exact rational parameter values that satisfy the side
conditions Williams states: the rule is applied (Lemma 7.1 merged or opening a block, Lemma 3.3 merged into
the innermost block, Lemma 7.2), and its output is compared component by component with the printed line,
once from the printed previous line and once from the line HY.Step produced. A printed superscript that is
omitted is compared with Williams's default (p. A:5) read block-wise: max{guess, 1}.

Output of the new log n block of Lemma 3.3 (l(o, e)), per display:
  p. A:31 example, Lemma 7.7 (base case and the inductive step k = 2, for d = 1 and d = 2), the 0,1,0 and
    0,0 slowdowns of p. A:36: only l = max(o, e) (HY.Step);
  Corollary 7.8 and the proof of Theorem 7.5 (p. A:34): l = max(o, e) and l = 1;
  annotation [1,1,0,0] (p. A:36), Case 1 (p. A:37), Case 2 (p. A:38): l = max(o, e), 1, max(o, 1), max(1, e).
The splice of Lemma 7.7's induction (the two existential blocks written as one, p. A:33) is not replayed.
Corollary 7.8 (used twice in the proof of Theorem 7.5) is a sub-derivation that Williams does not display;
it is constructed here from the rules (Lemma 7.1 merged, Lemma 3.3 merged, Lemma 7.2, repeated, then
Lemma 7.7's base case) and only its endpoint is compared: at the first use in the Theorem 7.5 sample it is the
line printed there; from 399 sample exponents under a block (A n^1)^1 (d = 1, c = 1.29) it is the corollary's
endpoint; at the second use it is the corollary's endpoint scaled by G = x + d(a-1),
(E n^G)^G (A log n)^l DTISP[n^G, n^(G d/(d+1))], which is not the line printed at that application
((E n^G)(A n) DTISP[...], with guess n for the universal block). The Theorem 7.5
sample satisfies the conditions printed on p. A:34 with a common epsilon. The 25-line proof of
pp. A:32-A:33 is replayed separately by w13_25line.py.

Each transition carries the asserted outcome from the printed previous line (agrees or differs) and, where the
paper's Appendix A states one, the formula for what HY.Step gives from the printed previous line; the script
asserts both, asserts that every display replayed under several outputs l has the same kernels under each, and
asserts the further checks named in the paper (the two-step derivation of the DTISP line of p. A:34 (D8), the
endpoints of the Corollary 7.8 sub-derivations (D7), the printed base case (D6), the 0,1,0 criterion and the
derivation of its first sample from DTIME_1[n^10] (D11), the absence of a Lemma 7.1 step with s = 0, the
examples of the paper's Section 2.4, item 3, Section 5.2 and Section 6 (a slowdown below Lemma 7.2's value that
meets the relaxed bound; a transition that is no single HL.RStep, HL.Loose or HL.Widen step but expands into three
exact steps; a [1,1,0,0] speedup outside Lemma 3.3's condition x <= a - 1 that is a single HL.RStep step), a sample
at which inequality (31) of Case 1 (p. A:37) fails, and a [1,1,0,0] sample with
x, y >= 0 outside the side conditions of Lemma 3.3 that no exact or relaxed speedup gives (D17), a [1,1,0,0]
sample outside only y <= a - 1 whose log n output fails the relaxed bound (D17), a [1,1,0,0] speedup whose log n
output is below max(o, e) (an HL.Loose step) and which expands into three relaxed steps at c = 4/3, a log n output
below max(HY.pin, e) on the empty prefix that is an RStep.speedN step, two Case 1 samples whose printed speedups are
HL.RStep steps and only HL.Loose steps (D12, D13), a Case 1 sample with e = 0 whose printed speedups, guess n^y
included, are HY.Step.speedMerge steps (D13), the rule membership of the Corollary 7.8 sub-derivations (D7: under
the output 1 the one at the second use is an HY.StepO path with l = 1, not an HY.Step path), and the relaxed
encoding of the line printed at the second use of Corollary 7.8 (D9)). It ends with the number of assertions that
hold; a failed one stops it.

The printed lines are transcribed from the rendered pages (the text layer loses superscripts and primes).

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


def traced_speed(line, x, ell, trace):
    new = speed(line, x, ell)
    if trace is not None:
        trace.append((line[0][-1][2], line[1][2], new[0][-1][2]))
    return new


def cor78(line, c, d, ell="max", trace=None):
    """Corollary 7.8 inside a prefix whose innermost block has output G = guess G: from (.., T G*A') with
    1 <= A' < eta, Lemma 7.7's rounds (Lemma 7.1 merged with s = G(A'-1), Lemma 3.3 merged so that the raised
    guess stays G, Lemma 7.2) until A' <= e_1, then the base case (s = G/(d+1), x = G(A'-1)). Returns the
    endpoint and the number of steps; appends (o, e, new log n output) of each Lemma 3.3 step to trace."""
    blocks, ker = line
    G = pin(blocks)
    e1 = Q(d + 2, d + 1)
    steps = 0
    while True:
        A1 = line[1][1] / G
        q = line[0][-1][0]
        if A1 <= e1:
            line = conv(line, G / (d + 1), d, q)
            line = traced_speed(line, G * (A1 - 1), ell, trace)
            return line, steps + 2
        A = c * (d + 1) * (A1 - 1)
        line = conv(line, G * (A1 - 1), d, q)
        line = traced_speed(line, G * (A1 - A / c), ell, trace)
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
KERNELS = {}
CHECKS = [0]


def check(cond, msg):
    """An assertion about a displayed transition; failures stop the script."""
    CHECKS[0] += 1
    if not cond:
        raise AssertionError(msg)


def run(title, start, trans, c, d, ell="max", key=None):
    """trans: list of (label, rule, printed, expect). The rule is applied to the printed previous line (omitted
    superscripts read block-wise) and to our previous line. expect is a dict with
      "agree": True/False, or a function of ell, the asserted outcome from the printed previous line;
      "hy":    a function of the output of the rule applied to the printed previous line that must return True
               (the formula of column 3 of the paper's Appendix A), with a description in "hy_text".
    Records the kernels of our lines under `key` so that runs of the same display under several outputs can be
    compared."""
    print(f"\n== {title} [l = {ELL[ell][0]}]")
    print(f"   start (printed): {show(start)}")
    ours = fill(start)
    prev_printed = start
    rows = []
    kers = [ours[1]]
    for label, rule, printed, exp in trans:
        from_p = None
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
        kers.append(ours[1])
        print(f"   {label}")
        print(f"     printed: {show(printed)}")
        print(f"     ours:    {show(ours)}")
        print("     from printed previous line: " + ("agrees" if not dp else "; ".join(dp)))
        print("     from our previous line:     " + ("agrees" if not do else "; ".join(do)))
        want = exp.get("agree")
        if callable(want):
            want = want(ell)
        if want is not None:
            check((not dp) == want, f"{title} [{ell}] {label}: expected {'agree' if want else 'differ'}, got {dp}")
        if "hy" in exp:
            check(from_p is not None and exp["hy"](from_p),
                  f"{title} [{ell}] {label}: HY.Step output {show(from_p) if from_p else None} is not "
                  f"{exp['hy_text']}")
            print(f"     asserted: HY.Step from the printed previous line gives {exp['hy_text']}")
        rows.append((label, dp))
        prev_printed = printed
    SUMMARY.append((title, ell, rows))
    if key is not None:
        KERNELS.setdefault(key, []).append((ell, kers))
    return ours


def P(blocks, ker):
    return ([tuple(b) for b in blocks], ker)


def T(line):
    return line[1][1] if line[1][0] == "T" else None


AG = {"agree": True}


def example_a31():
    c, d = Q(6, 5), 1
    L0 = P([], ("T", Q(3, 2)))
    run("p. A:31, Example (Kannan, van Melkebeek-Raz), d = 1, c = 6/5", L0, [
        ("Lemma 7.1, s = 1/2", lambda L: conv(L, Q(1, 2), d),
         P([("E", Q(1), None)], ("S", Q(3, 2), Q(1, 2))), AG),
        ("Lemma 3.3, x = 1/2", lambda L: speed(L, Q(1, 2)),
         P([("E", Q(1), None), ("A", Q(0), None)], ("S", Q(1), Q(1, 2))),
         {"agree": True, "hy": lambda L: L[0][-1][2] == 1, "hy_text": "log n output max(1, 1/2) = 1"}),
        ("Lemma 7.2 (removes the (A log n) block)", lambda L: slow(L, c), P([("E", Q(1), None)], ("T", c)),
         {"agree": True, "hy": lambda L: T(L) == c, "hy_text": "c max(1, 1, 0, 1) = c"}),
        ("Lemma 7.2", lambda L: slow(L, c), P([], ("T", c * c)), AG),
    ], c, d)


def lemma77():
    for d in (1, 2):
        c = Q(129, 100) if d == 1 else Q(118, 100)
        e = [None, Q(d + 2, d + 1)]
        for _ in range(3):
            e.append(1 + e[-1] / (c * (d + 1)))
        dd = Q(d, d + 1)
        run(f"p. A:33, Lemma 7.7 base case, d = {d}, c = {c}", P([], ("T", e[1])), [
            ("Lemma 7.1, s = 1/(d+1)", lambda L: conv(L, Q(1, d + 1), d), P([("E", Q(1), None)], ("S", e[1], dd)),
             {"agree": True, "hy": lambda L: L[0][-1][2] == 1, "hy_text": "output 1"}),
            ("Lemma 3.3, x = 1/(d+1)", lambda L: speed(L, Q(1, d + 1)),
             P([("E", Q(1), None), ("A", Q(0), None)], ("S", Q(1), dd)),
             {"agree": True, "hy": lambda L: L[0][-1][2] == max(Q(1), dd) == 1,
              "hy_text": "log n output max(1, d/(d+1)) = 1"}),
        ], c, d)
        k = 2
        a = 1 + e[k] / (c * (d + 1))
        s = e[k] / (c * (d + 1))
        x = a - e[k] / c
        eta = 1 + 1 / (c * (d + 1) - 1)
        check(e[k] < eta and d * eta / (c * (d + 1)) <= 1, "Lemma 7.7 sample: e_k < eta, d eta/(c(d+1)) <= 1")
        run(f"p. A:33, Lemma 7.7 inductive step, k = {k}, d = {d}, c = {c}", P([], ("T", a)), [
            ("Lemma 7.1, s = e_k/(c(d+1))", lambda L: conv(L, s, d), P([("E", Q(1), None)], ("S", a, d * s)), AG),
            ("Lemma 3.3, x = 1 + e_k/(c(d+1)) - e_k/c", lambda L: speed(L, x),
             P([("E", Q(1), None), ("A", Q(0), None)], ("S", e[k] / c, d * s)),
             {"agree": True, "hy": lambda L: L[0][-2][1] == x + d * s == 1
              and L[0][-1][2] == max(Q(1), d * e[k] / (c * (d + 1))) == 1,
              "hy_text": "guess x + e = 1 and log n output max(1, d e_k/(c(d+1))) = 1"}),
            ("Lemma 7.2", lambda L: slow(L, c), P([("E", Q(1), None)], ("T", e[k])),
             {"agree": True, "hy": lambda L: T(L) == c * max(Q(1), Q(1), Q(0), e[k] / c) == e[k],
              "hy_text": "c max(1, 1, 0, e_k/c) = e_k"}),
        ], c, d)


def theorem75():
    d, c = 1, Q(129, 100)
    a, x = Q(17617, 10000), Q(2583, 10000)
    G = x + d * (a - 1)
    eta = c * (d + 1) / (c * (d + 1) - 1)
    es = c * ((d + 1) * (a - 1) - x)
    e2 = c * c / G
    eps = eta - e2
    t1 = 1 - d * (a - 1)
    t = a - x - t1
    dd = Q(d, d + 1)
    print(f"\n   Theorem 7.5 parameters: d = {d}, c = {c}, a = {a}, x = {x}; eta = 1 + 1/(c(d+1)-1) = {eta}")
    print(f"     c >= x + d(a-1) = {G} >= 1: {c >= G >= 1}; 1 - d(a-1) = {t1} >= 0: {t1 >= 0}")
    print(f"     printed conditions (p. A:34) with the common epsilon = eta - c^2/(x+d(a-1)) = {eps} > 0: {eps > 0};"
          f" c((d+1)(a-1) - x) = {es} >= eta - epsilon = {e2}: {es >= e2}")
    print(f"     Corollary 7.8 needs exponents below eta: c((d+1)(a-1) - x) < eta: {es < eta}, "
          f"c^2/(x+d(a-1)) < eta: {e2 < eta}")
    print(f"     c - 1/(d+1) = {c - Q(1, d + 1)} <= 1 (the hypothesis of HY.slow_convMerge_A34): {c - Q(1, d + 1) <= 1}")
    check(c >= G >= 1 and t1 >= 0 and eps > 0 and es >= e2 and es < eta and e2 < eta and c < Q(d + 2, d + 1)
          and t >= 1, "Theorem 7.5 sample conditions")
    first_end = P([("E", G, G), ("A", Q(1), Q(1)), ("E", Q(0), Q(1))], ("S", Q(1), dd))
    for ell in ("max", "one"):
        lo = ELL[ell][1]
        scaled = P([("E", G, G), ("A", Q(0), lo(G, G * dd))], ("S", G, G * dd))
        printed_second = P([("E", G, None), ("A", Q(1), None)], ("S", G, G * dd))
        Ln = run(f"p. A:34, proof of Theorem 7.5, d = {d}, c = {c}", P([], ("T", a)), [
            ("Lemma 7.1, s = a-1", lambda L: conv(L, a - 1, d), P([("E", Q(1), None)], ("S", a, d * (a - 1))),
             {"agree": True, "hy": lambda L: L[0][-1][2] == 1, "hy_text": "output 1"}),
            ("Lemma 3.3 (Speedup), x", lambda L: speed(L, x, ell),
             P([("E", G, G), ("A", Q(0), Q(1))], ("S", a - x, d * (a - 1))),
             {"agree": True, "hy": lambda L: L[0][-1][2] == lo(Q(1), d * (a - 1)) == 1,
              "hy_text": "log n output l(1, d(a-1)) = 1 (D4: d(a-1) <= 1)"}),
            ("Lemma 3.3 (Speedup), x' = 1-d(a-1)", lambda L: speed(L, t1, ell),
             P([("E", G, G), ("A", t1 + d * (a - 1), Q(1)), ("E", Q(0), Q(1))], ("S", a - x - t1, d * (a - 1))),
             {"agree": True, "hy": lambda L: L[0][-1][2] == lo(Q(1), d * (a - 1)) == 1,
              "hy_text": "log n output l(1, d(a-1)) = 1"}),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c),
             P([("E", G, G), ("A", Q(1), Q(1))], ("T", c * t)),
             {"agree": True, "hy": lambda L: T(L) == c * max(Q(1), Q(1), Q(0), t) == c * t,
              "hy_text": "c max(1, 1, 0, a-x-(1-d(a-1))) = c(a-x-(1-d(a-1))) (D5: that time is >= 1)"}),
            ("Corollary 7.8 (sub-derivation; first use)", lambda L: cor78(L, c, d, ell)[0],
             P([("E", G, None), ("A", Q(1), None), ("E", Q(0), None)], ("S", Q(1), dd)),
             {"agree": True, "hy": lambda L: L == first_end,
              "hy_text": "exactly the printed line, outputs G, 1, 1 (D7)"}),
            ("Lemma 7.2 (Slowdown) printed with a DTISP kernel", lambda L: slow(L, c),
             P([("E", G, None), ("A", Q(1), None)], ("S", c, dd)),
             {"agree": False, "hy": lambda L: L == P([("E", G, G), ("A", Q(1), Q(1))], ("T", c)),
              "hy_text": "(E n^G)^G (A n)^1 DTIME_d[n^c] (D8)"}),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([("E", G, G)], ("T", c * c)),
             {"agree": True, "hy": lambda L: T(L) == c * max(G, Q(1), Q(1), c) == c * c,
              "hy_text": "c max(G, 1, 1, c) = c^2"}),
            ("Corollary 7.8 at scale x+d(a-1) (sub-derivation; second use)", lambda L: cor78(L, c, d, ell)[0],
             printed_second,
             {"agree": False, "hy": lambda L: L == scaled,
              "hy_text": "the scaled endpoint (E n^G)^G (A log n)^l DTISP[n^G, n^(G d/(d+1))], "
                         f"l = {lo(G, G * dd)} (D7, D9)"}),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([("E", G, None)], ("T", c * G)),
             {"agree": True, "hy": lambda L: T(L) == c * G, "hy_text": "c G"}),
            ("Lemma 7.2 (Slowdown)", lambda L: slow(L, c), P([], ("T", c * c * G)),
             {"agree": True, "hy": lambda L: T(L) == c * max(Q(1), G, G, c * G) == c * c * G,
              "hy_text": "c max(1, G, G, cG) = c^2 G"}),
        ], c, d, ell, key="thm75")
        check(Ln[1][1] == c * c * G < a, "Theorem 7.5 sample: final exponent")
        print(f"   final exponent {Ln[1][1]} = {float(Ln[1][1]):.6f} < a = {a}: {Ln[1][1] < a}")
        got = cor78(P([("E", G, G)], ("T", c * c)), c, d, ell)[0]
        check(got == scaled and compare(got, printed_second) != [],
              "second use of Corollary 7.8: the scaled endpoint is reached and differs from the printed line")
        if ell == "one":
            check(renc(fill(printed_second)) == renc(scaled),
                  "D9: the printed line has the same relaxed encoding as the endpoint reached with output 1")
            print(f"   D9: with output 1 the printed line {show(printed_second)} and the endpoint {show(scaled)} have the"
                  f" same relaxed encoding {rshow(renc(scaled))} (asserted)")
        print(f"   second use of Corollary 7.8: the derivation reaches the scaled corollary endpoint {show(scaled)}"
              f" exactly; the line printed at the application, {show(printed_second)}, differs from it:"
              f" {'; '.join(compare(got, printed_second))} (asserted)")
    # D7: rule membership of the two sub-derivations. HY.Step.speedMerge gives the new log n block max(o, e).
    for ell in ("max", "one"):
        tr1, tr2 = [], []
        cor78(P([("E", G, G), ("A", Q(1), Q(1))], ("T", es)), c, d, ell, tr1)
        cor78(P([("E", G, G)], ("T", c * c)), c, d, ell, tr2)
        check(all(lo == max(o, e) == 1 for o, e, lo in tr1), "D7: first use, an HY.Step path under both outputs")
        check(all(o == G > e for o, e, lo in tr2) and tr2[-1][:2] == (G, G * dd)
              and all(lo == (G if ell == "max" else 1) for o, e, lo in tr2),
              "D7: second use, outputs of the Lemma 3.3 steps")
    check(c < Q(6547, 5000) and c * c < 2, "D7: c = 1.29 is below both d = 1 ceiling hypotheses")
    print(f"   D7: at the first use every Lemma 3.3 step has max(o, e) = 1, so the replays with max(o, e) and with"
          f" output 1 are the same HY.Step path; at the second use each of the {len(tr2)} Lemma 3.3 steps has o = G ="
          f" {G} > e (the last e = {G * dd}), so HY.Step.speedMerge gives the new log n block output G, and the"
          f" replay with output 1 is an HY.StepO path with l = 1, not an HY.Step path, each such step below the"
          f" HL.RStep.speedM floor max(HL.pin, e) = G; c = {c} is below 6547/5000 and c^2 < 2, so these samples"
          " check rule membership only (asserted)")
    # D8: the printed DTISP line is reached by Lemma 7.2 followed by Lemma 7.1 merged with s = 1/(d+1)
    L5 = first_end
    L6 = slow(L5, c)
    L7 = conv(L6, Q(1, d + 1), d, "A")
    target = fill(P([("E", G, None), ("A", Q(1), None)], ("S", c, dd)))
    check(L7 == target, "D8: Lemma 7.2 then Lemma 7.1 merged (s = 1/(d+1)) reaches the printed line")
    print(f"   D8: from {show(L5)}, Lemma 7.2 gives {show(L6)} and Lemma 7.1 merged with s = 1/(d+1) gives"
          f" {show(L7)}, the printed line with its omitted superscripts read block-wise (asserted;"
          f" HY.slow_convMerge_A34 in Lean)")
    n1 = cor78(([("E", G, G), ("A", Q(1), Q(1))], ("T", es)), c, d)[1]
    n2 = cor78(([("E", G, G)], ("T", c * c)), c, d)[1]
    print(f"   the two Corollary 7.8 sub-derivations have {n1} and {n2} steps")
    bad = []
    for k in range(1, 400):
        A1 = 1 + (eta - 1) * Q(k, 400)
        try:
            end = cor78(([("A", Q(1), Q(1))], ("T", A1)), c, d)[0]
            if end != ([("A", Q(1), Q(1)), ("E", Q(0), Q(1))], ("S", Q(1), dd)):
                bad.append(A1)
        except RuleError:
            bad.append(A1)
    check(not bad, f"Corollary 7.8 samples: {bad[:3]}")
    print(f"   Corollary 7.8 endpoint (A n)^1 (E log)^1 DTISP[n, n^(d/(d+1))] reached exactly from DTIME_d[n^A'] "
          f"for A' = 1 + (eta-1)k/400, k = 1..399: {'all (asserted)' if not bad else 'fails at ' + str(bad[:3])}")


def cor78_base_printed():
    """The base case printed in the proof of Corollary 7.8, DTIME_d[n^((d+1)/(d+2))]: from it HY.Step allows only
    Lemma 7.1 (time unchanged); after it Lemma 3.3 (a >= 1), Lemma 7.2 (time >= 1) and Lemma 7.1 (DTIME_d kernel)
    do not apply. Checked for d = 1, 2, 3 at s = t/2 and s = t."""
    for d in (1, 2, 3):
        t = Q(d + 1, d + 2)
        L0 = ([], ("T", t))
        res = []
        for s in (t / 2, t):
            L1 = conv(L0, s, d)
            for name, f in (("Lemma 3.3, x = 0", lambda L: speed(L, Q(0))), ("Lemma 7.2", lambda L: slow(L, Q(3, 2))),
                            ("Lemma 7.1", lambda L: conv(L, t / 2, d))):
                try:
                    f(L1)
                    res.append(f"{name} applies after s = {s}")
                except RuleError:
                    pass
        check(not res, f"D6, d = {d}: {res}")
        print(f"   p. A:34, printed base case DTIME_{d}[n^{t}]: after Lemma 7.1 no rule applies: "
              + ("yes (asserted)" if not res else "; ".join(res)))


def thm79_1100():
    for d, c, a, x, y in ((1, Q(3, 2), Q(4), Q(1), Q(1)), (1, Q(3, 2), Q(3), Q(1, 2), Q(2)),
                          (2, Q(4, 3), Q(5), Q(2), Q(1, 2))):
        check(0 < x <= a and a >= 1 and 0 <= y <= a - 1 and d * x <= a - y,
              "[1,1,0,0] sample: 0 < x <= a, a >= 1, 0 <= y <= a-1, dx <= a-y")
        m = max(a - x, y + d * x, Q(1), a - y)
        for ell in ELL:
            lo = ELL[ell][1](max(a - x, Q(1)), d * x)
            run(f"p. A:36, Theorem 7.9, annotation [1,1,0,0], d = {d}, c = {c}, a = {a}, x = {x}, y = {y}",
                P([], ("T", a)), [
                    ("Lemma 7.1, s = x", lambda L: conv(L, x, d),
                     P([("E", a - x, max(a - x, Q(1)))], ("S", a, d * x)), AG),
                    ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                     P([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))],
                       ("S", a - y, d * x)),
                     {"agree": lo == 1, "hy": lambda L: L[0][-1][2] == lo
                      and (ell != "max" or lo == max(a - x, Q(1), d * x)),
                      "hy_text": f"log n output l(max(a-x,1), dx) = {lo}" + (" = max(a-x, 1, dx)" if ell == "max"
                                                                              else "")}),
                    ("Lemma 7.2", lambda L: slow(L, c),
                     P([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1)))], ("T", c * m)),
                     {"agree": True, "hy": lambda L: T(L) == c * m, "hy_text": "c max{a-x, y+dx, 1, a-y}"}),
                    ("Lemma 7.2", lambda L: slow(L, c), P([], ("T", c * c * m)),
                     {"agree": True, "hy": lambda L: T(L) == c * max(Q(1), max(a - x, y + d * x, Q(1)),
                                                                      max(a - x, y + d * x), c * m) == c * c * m,
                      "hy_text": "c max(1, max{a-x,y+dx,1}, max{a-x,y+dx}, c m) = c^2 max{a-x, y+dx, 1, a-y}"}),
                ], c, d, ell, key=("1100", d, a, x, y))
    for d, a in ((1, Q(4)), (2, Q(5))):
        try:
            conv(([], ("T", a)), Q(0), d)
            ok = False
        except RuleError:
            ok = True
        check(ok, "x = 0: HY.Step has no Lemma 7.1 step with s = 0")
    print("\n   [1,1,0,0] at x = 0: HY.Step has no Lemma 7.1 step with s = 0 (asserted, d = 1, 2);"
          " HL.RStep.convN allows s = 0")


def thm79_1100_side():
    """Row D17: the [1,1,0,0] display of p. A:36 is stated for x, y >= 0 only. At d = 1, a = 4, x = 3, y = 2 its
    Lemma 3.3 step goes from (E n^1)^1 DTISP[n^4, n^3] to (E n^5)^5 (A n^0)^1 DTISP[n^2, n^3]: dx = 3 > a - y = 2,
    so HY.Step has no such step (e <= a - x fails), and no relaxed speedup (HL.RStep speedM/speedN, HL.Loose)
    either: each needs e <= a - x <= a2, i.e. new time >= old space."""
    d, a, x, y = 1, Q(4), Q(3), Q(2)
    L1 = conv(([], ("T", a)), x, d)
    check(L1 == ([("E", Q(1), Q(1))], ("S", a, Q(3))), "D17: Lemma 7.1 step")
    printed = ([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))], ("S", a - y, d * x))
    check(printed == ([("E", Q(5), Q(5)), ("A", Q(0), Q(1))], ("S", Q(2), Q(3))), "D17: printed line")
    try:
        speed(L1, y)
        exact = True
    except RuleError:
        exact = False
    old_space, new_time = L1[1][2], printed[1][1]
    check(not exact and d * x > a - y, "D17: no HY.Step speedup (dx > a - y)")
    check(new_time < old_space, "D17: no relaxed speedup (new time 2 below old space 3)")
    print(f"\n== p. A:36, [1,1,0,0] at d = {d}, a = {a}, x = {x}, y = {y} (Williams: x, y >= 0): from {show(L1)} the display"
          f" gives {show(printed)}; dx = {d * x} > a - y = {a - y}, so no HY.Step speedup, and new time {new_time} < old"
          f" space {old_space}, so no relaxed speedup (asserted; row D17)")


def thm79_010():
    print("\n   The 0,1,0 display of p. A:36 (Lemma 7.2 maximum printed without b'):")
    for d, c, bp, ap, b, a, s, rel_exp in ((1, Q(3, 2), Q(10), Q(5), Q(5), Q(15, 2), Q(15, 4), "below"),
                                           (1, Q(3, 2), Q(2), Q(3), Q(3), Q(4), Q(1), "equal to"),
                                           (2, Q(3, 2), Q(1), Q(1), Q(1), Q(2), Q(2), "above"),
                                           (2, Q(3, 2), Q(3), Q(1), Q(1), Q(2), Q(2), "above")):
        start = P([("A", Q(0), bp), ("E", ap, b)], ("T", a))
        full = c * max(bp, b, a - s, ap, a)
        disp = max(c * b, c * a - c * s, c * ap, c * a, c * d * s)
        full00 = c * max(bp, b, ap, a)
        disp00 = max(c * b, c * a, c * ap)
        run(f"p. A:36, 0,1,0, d = {d}, c = {c}, b' = {bp}, a' = {ap}, b = {b}, a = {a}, s = {s}", start, [
            ("Lemma 7.1 (merged), s", lambda L: conv(L, s, d),
             P([("A", Q(0), bp), ("E", max(ap, a - s), max(b, a - s))], ("S", a, d * s)), AG),
            ("Lemma 7.2", lambda L: slow(L, c),
             P([("A", Q(0), bp)], ("T", disp)),
             {"agree": disp == full, "hy": lambda L: T(L) == full, "hy_text": f"c max(b', b, a-s, a', a) = {full}"}),
        ], c, d)
        L1 = conv(start, s, d)
        print(f"     Lemma 7.2 with the printed maximum (without b'): {show(slow(L1, c, omit_bk=True))}")
        rel = "above" if disp > full else "below" if disp < full else "equal to"
        check(rel == rel_exp, f"0,1,0 sample: displayed exponent {rel} Lemma 7.2's, expected {rel_exp}")
        check((disp < full) == (bp > max(b, a - s, ap, a, d * s)),
              "0,1,0: below exactly when b' > max{b, a-s, a', a, ds}")
        check((disp00 < full00) == (bp > max(b, ap, a)), "0,0: below exactly when b' > max{b, a', a}")
        rel010 = c * max(bp, max(b, a - s), a)
        rel00 = c * max(bp, b, a)
        check((disp < rel010) == (disp < full) and (disp00 < rel00) == (disp00 < full00),
              "0,1,0 and 0,0: below the HL.RStep.slow bound c max(pin rest, b, time k) exactly when below Lemma 7.2")
        bstrict = bp > max(b, a - s, ap, a)
        print(f"     HL.RStep.slow bound c max(b', max(b, a-s), a) = {rel010} (0,1,0), c max(b', b, a) = {rel00} (0,0):"
              f" the display is below it exactly when it is below Lemma 7.2's value (asserted)")
        print(f"     displayed exponent {disp} is {rel} Lemma 7.2's {full} (asserted); b' is the strict maximum of"
              f" Lemma 7.2: {bstrict}; b' > max(b, a-s, a', a, ds): {bp > max(b, a - s, ap, a, d * s)}")
        run(f"p. A:36, 0,0 comparison, same parameters", start, [
            ("Lemma 7.2", lambda L: slow(L, c), P([("A", Q(0), bp)], ("T", disp00)),
             {"agree": disp00 == full00, "hy": lambda L: T(L) == full00,
              "hy_text": f"c max(b', b, a', a) = {full00}"}),
        ], c, d)
    # the first sample's starting line is reachable from DTIME_1[n^10] (with the quantifiers exchanged)
    d, c = 1, Q(3, 2)
    L = ([], ("T", Q(10)))
    L = conv(L, Q(5), d, "E")
    L = speed(L, Q(5))
    L = speed(L, Q(0))
    L = slow(L, c)
    want = ([("E", Q(10), Q(10)), ("A", Q(5), Q(5))], ("T", Q(15, 2)))
    check(L == want, "0,1,0 sample 1 reachable")
    L1 = conv(L, Q(15, 4), d, "A")
    L2 = slow(L1, c)
    check(L2 == ([("E", Q(10), Q(10))], ("T", Q(15))), "0,1,0 sample 1: Lemma 7.2 gives 15")
    print(f"   reachability of the first sample: DTIME_1[n^10], Lemma 7.1 (s = 5), Lemma 3.3 (x = 5), Lemma 3.3"
          f" (x = 0, merged), Lemma 7.2 give {show(L)}; Lemma 7.1 merged (s = 15/4) gives {show(L1)} and Lemma 7.2"
          f" gives {show(L2)}, where the display gives 45/4 (asserted)")


def thm79_case1():
    for d, c, b, ap, a, e, x, y in ((1, Q(3, 2), Q(2), Q(1), Q(8), Q(3), Q(1), Q(1)),
                                    (1, Q(3, 2), Q(4), Q(2), Q(8), Q(1), Q(2), Q(1)),
                                    (1, Q(3, 2), Q(2), Q(2), Q(6), Q(1, 2), Q(3), Q(1, 2)),
                                    (1, Q(3, 2), Q(2), Q(10), Q(6), Q(1, 2), Q(3), Q(1, 2))):
        m3 = max(b, y + e, Q(1), a - x - y)
        hy4 = c * max(b, x + e, c * m3)
        disp4 = c * c * max(b, y + e, Q(1), x + e, a - x - y)
        check(disp4 >= hy4, "Case 1: the last displayed slowdown is at least Lemma 7.2's value")
        for ell in ELL:
            lo1 = ELL[ell][1](b, e)
            lo2 = ELL[ell][1](max(b, Q(1)), e)
            start = P([("A", Q(0), b), ("E", ap, b)], ("S", a, e))
            run(f"p. A:37, Case 1, d = {d}, c = {c}, b = {b}, a' = {ap}, a = {a}, e = {e}, x = {x}, y = {y}",
                start, [
                    ("Lemma 3.3, x", lambda L: speed(L, x, ell),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", Q(0), max(b, Q(1)))],
                       ("S", a - x, e)),
                     {"agree": lo1 == max(b, Q(1)), "hy": lambda L: L[0][-1][2] == lo1,
                      "hy_text": f"log n output l(b, e) = {lo1}"}),
                    ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", y, max(b, y + e, Q(1))),
                        ("E", Q(0), max(b, Q(1)))], ("S", a - x - y, e)),
                     {"agree": False, "hy": lambda L: L[0][-2][1] == y + e and L[0][-1][2] == lo2,
                      "hy_text": f"guess of Q2 y+e = {y + e}, output of Q3 l(b, e) = {lo2}"}),
                    ("Lemma 7.2", lambda L: slow(L, c),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", y, max(b, y + e, Q(1)))],
                       ("T", c * m3)),
                     {"agree": True, "hy": lambda L: T(L) == c * m3, "hy_text": "c max{b, y+e, 1, a-x-y}"}),
                    ("Lemma 7.2 (removes Q2; Q1 remains)", lambda L: slow(L, c),
                     P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e))], ("T", disp4)),
                     {"agree": disp4 == hy4, "hy": lambda L: T(L) == hy4 and len(L[0]) == 2,
                      "hy_text": f"c max(b, x+e, c max{{b, y+e, 1, a-x-y}}) = {hy4} (a' does not enter)"}),
                ], c, d, ell, key=("case1", b, ap, a, e, x, y))
            run("p. A:37, Case 1, the string 1,0, same parameters", start, [
                ("Lemma 3.3, x", lambda L: speed(L, x, ell),
                 P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e)), ("A", Q(0), max(b, Q(1)))],
                   ("S", a - x, e)),
                 {"agree": lo1 == max(b, Q(1)), "hy": lambda L: L[0][-1][2] == lo1,
                  "hy_text": f"log n output l(b, e) = {lo1}"}),
                ("Lemma 7.2", lambda L: slow(L, c),
                 P([("A", Q(0), b), ("E", max(ap, x + e), max(b, x + e))],
                   ("T", c * max(b, Q(1), x + e, a - x))),
                 {"agree": True, "hy": lambda L: T(L) == c * max(b, Q(1), x + e, a - x),
                  "hy_text": "c max{b, 1, x+e, a-x}"}),
            ], c, d, ell, key=("case1-10", b, ap, a, e, x, y))
        print(f"   Case 1 sample b = {b}, a' = {ap}: last slowdown HY.Step {hy4} = {float(hy4):g}, display {disp4} ="
              f" {float(disp4):g}; the display is at least Lemma 7.2's value (asserted)")


def thm79_case2():
    for d, c, b, ap, a, x, y in ((1, Q(3, 2), Q(2), Q(1), Q(6), Q(2), Q(1)),
                                 (1, Q(3, 2), Q(1), Q(5), Q(4), Q(1), Q(1, 2))):
        m = max(a - x, y + d * x, b, a - y)
        hy4 = c * max(ap, c * m)
        disp4 = c * c * max(ap, a - x, y + d * x, b, a - y)
        check(disp4 >= hy4, "Case 2: the last displayed slowdown is at least Lemma 7.2's value")
        for ell in ELL:
            lo = ELL[ell][1](max(b, a - x), d * x)
            start = P([("A", Q(0), b), ("E", ap, b)], ("T", a))
            run(f"p. A:38, Case 2, d = {d}, c = {c}, b = {b}, a' = {ap}, a = {a}, x = {x}, y = {y}", start, [
                ("Lemma 7.1 (merged), s = x", lambda L: conv(L, x, d),
                 P([("A", Q(0), b), ("E", max(ap, a - x), max(b, a - x))], ("S", a, d * x)), AG),
                ("Lemma 3.3, y", lambda L: speed(L, y, ell),
                 P([("A", Q(0), b), ("E", max(ap, a - x, y + d * x), max(a - x, y + d * x, b)), ("A", Q(0), Q(1))],
                   ("S", a - y, d * x)),
                 {"agree": lo == 1, "hy": lambda L: L[0][-1][2] == lo
                  and (ell != "max" or lo == max(b, a - x, d * x)),
                  "hy_text": f"log n output l(max(b,a-x), dx) = {lo}" + (" = max(b, a-x, dx)" if ell == "max"
                                                                         else "")}),
                ("Lemma 7.2", lambda L: slow(L, c),
                 P([("A", Q(0), b), ("E", max(ap, a - x, y + d * x), max(a - x, y + d * x, b))], ("T", c * m)),
                 {"agree": True, "hy": lambda L: T(L) == c * m, "hy_text": "c max{a-x, y+dx, b, a-y}"}),
                ("Lemma 7.2 (removes Q1)", lambda L: slow(L, c),
                 P([("A", Q(0), b)], ("T", disp4)),
                 {"agree": disp4 == hy4, "hy": lambda L: T(L) == hy4,
                  "hy_text": f"c max(a', c max{{a-x, y+dx, b, a-y}}) = {hy4}"}),
            ], c, d, ell, key=("case2", b, ap, a, x, y))
            run("p. A:38, Case 2, the string 0 (inline: c max{a, a', b}), same parameters", start, [
                ("Lemma 7.2", lambda L: slow(L, c), P([("A", Q(0), b)], ("T", c * max(a, ap, b))),
                 {"agree": True, "hy": lambda L: T(L) == c * max(a, ap, b), "hy_text": "c max{a, a', b}"}),
            ], c, d, ell)


def slow_relaxed_test():
    """Paper Section 6: the relaxed slowdown HL.RStep.slow requires a' >= c max(pin rest, b, time k) and drops
    the guess of the removed block. Remaining output, removed output and kernel time 1, removed guess 5: Lemma
    7.2 gives 5c, the relaxed bound is c, so a time in [c, 5c) is below Lemma 7.2's value but an HL.RStep step."""
    c = Q(3, 2)
    line = P([("E", Q(1), Q(1)), ("A", Q(5), Q(1))], ("T", Q(1)))
    exact = T(slow(line, c))
    bound = c * max(pin(line[0][:-1]), line[0][-1][2], line[1][1])
    check(exact == 5 * c and bound == c, "Section 6: slowdown with the removed guess the unique maximum")
    print(f"\n== Paper Section 6: slowdown of {show(line)} at c = {c}: Lemma 7.2 gives {exact} = 5c, the relaxed bound"
          f" c max(pin rest, b, time k) is {bound} = c (asserted)")


def rpin(outs):
    """Input superscript of a relaxed line (HL.pin): the innermost output, or 0 for the empty prefix."""
    return outs[-1] if outs else Q(0)


def enc(line):
    """The relaxed encoding HL.enc: the output superscripts (outermost first here) and the kernel."""
    return [b[2] for b in line[0]], line[1]


def rslow_bound(line, c):
    """The least time HL.RStep.slow allows after removing the innermost block: c max(pin rest, b, time k)."""
    outs, ker = enc(line)
    return c * max(rpin(outs[:-1]), outs[-1], ker[1])


def rspeedM_ok(src, dst, x):
    """HL.RStep.speedM from the encoding of src to that of dst with parameter x: 0 <= x, e <= a - x,
    max(b, x + e) <= b', max(b, e) <= L, a - x <= a2, e <= e2, and the outer outputs unchanged."""
    (outs, (_, a, e)), (outs2, (_, a2, e2)) = enc(src), enc(dst)
    b, (b1, L) = outs[-1], outs2[-2:]
    return (outs2[:-2] == outs[:-1] and 0 <= x and e <= a - x and max(b, x + e) <= b1 and max(b, e) <= L
            and a - x <= a2 and e <= e2)


def expansion_example():
    """Paper Section 6: a transition that is no single HL.RStep, HL.Loose or HL.Widen step (a single relaxed
    slowdown would need a larger time; HL.Loose and HL.Widen give DTISP kernels) but expands into exact steps. d = 1,
    c = 10/7: Lemma 7.1 (s = 1) takes DTIME_1[n^3] to (E n^2)^2 DTISP[n^3, n^1]; a single relaxed slowdown from
    there needs time >= c max(0, 2, 3) = 30/7, while Lemma 3.3 (x = 1) and two Lemma 7.2 steps reach
    DTIME_1[n^(2c^2)] = DTIME_1[n^(200/49)], and 200/49 < 30/7."""
    d, c = 1, Q(10, 7)
    L1 = conv(([], ("T", Q(3))), Q(1), d)
    bound = rslow_bound(L1, c)
    L2 = speed(L1, Q(1))
    L3 = slow(L2, c)
    L4 = slow(L3, c)
    check(L1 == ([("E", Q(2), Q(2))], ("S", Q(3), Q(1))) and bound == Q(30, 7), "Section 6 expansion: start")
    check(L4 == ([], ("T", 2 * c * c)) and 2 * c * c == Q(200, 49) and Q(200, 49) < bound,
          "Section 6 expansion: three exact steps reach a time below the single-step relaxed bound")
    print(f"\n== Paper Section 6: from {show(L1)} (d = 1, c = 10/7) a single relaxed slowdown needs time >= {bound};"
          f" Lemma 3.3 (x = 1) and two Lemma 7.2 steps give {show(L2)}, {show(L3)}, {show(L4)}: time 200/49 < 30/7"
          " (asserted)")


def speed_outside_a36():
    """Paper Section 6: a [1,1,0,0] speedup of p. A:36 outside Lemma 3.3's side conditions that is still a single
    HL.RStep step. d = 1, a = 3/2, x = 1/2, y = 3/4: y > a - 1 (so no HY.Step speedup, and the new time 3/4 is
    below 1), but e = dx = 1/2 <= a - y, and the printed line is an HL.RStep.speedM step from the Lemma 7.1 line."""
    d, a, x, y = 1, Q(3, 2), Q(1, 2), Q(3, 4)
    L1 = conv(([], ("T", a)), x, d)
    printed = ([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))], ("S", a - y, d * x))
    try:
        speed(L1, y)
        exact = True
    except RuleError:
        exact = False
    check(L1 == ([("E", Q(1), Q(1))], ("S", a, Q(1, 2))) and y > a - 1 and d * x <= a - y, "A:36 sample a = 3/2")
    check(not exact and rspeedM_ok(L1, printed, y), "A:36 sample a = 3/2: no HY.Step speedup, but HL.RStep.speedM")
    print(f"\n== p. A:36, [1,1,0,0] at d = {d}, a = {a}, x = {x}, y = {y}: y > a - 1, so no HY.Step speedup; from"
          f" {show(L1)} the display gives {show(printed)}, an HL.RStep.speedM step (asserted)")


def r_step_any(src, dst, c, d, loose=False):
    """Whether one HL.RStep c d step (with loose=True: one HL.Loose step, i.e. speedM/speedN with the bound on
    the new log n block's output replaced by >= 0) takes the relaxed line src to dst. Relaxed lines are
    (outputs, kernel), outputs outermost first (HL.RLine lists them innermost first); HL.pin of the empty prefix
    is 0. The only constructor whose shape matches is tested, with the best parameter."""
    (o0, k0), (o1, k1) = src, dst
    if k1[0] == "T":
        return (not loose and len(o0) >= 1 and o1 == o0[:-1]
                and c * max(rpin(o0[:-1]), o0[-1], k0[1]) <= k1[1])
    if k0[0] == "T":
        if loose:
            return False
        a, a2, e = k0[1], k1[1], k1[2]
        s = min(a, e / d) if d > 0 else a
        if not (0 <= s <= a and a <= a2 and d * s <= e):
            return False
        if len(o1) == len(o0) and o0:
            return o1[:-1] == o0[:-1] and max(o0[-1], a - s) <= o1[-1]
        return len(o1) == len(o0) + 1 and o1[:-1] == o0 and max(rpin(o0), a - s) <= o1[-1]
    a, e, a2, e2 = k0[1], k0[2], k1[1], k1[2]
    if len(o1) == len(o0) + 1 and o0:
        b, b1, L = o0[-1], o1[-2], o1[-1]
        ok_rest = o1[:-2] == o0[:-1]
    elif len(o1) == len(o0) + 2:
        b, b1, L = rpin(o0), o1[-2], o1[-1]
        ok_rest = o1[:-2] == o0
    else:
        return False
    lo, hi = max(Q(0), a - a2), min(a - e, b1 - e)
    return (ok_rest and lo <= hi and b <= b1 and e <= e2
            and (L >= 0 if loose else max(b, e) <= L))


def rshow(rl):
    """A relaxed line in HL order (outputs innermost first), e.g. ([1, 3/2], S 3/2 3/2)."""
    outs, ker = rl
    return f"([{', '.join(str(o) for o in reversed(outs))}], {ker[0]} {' '.join(str(v) for v in ker[1:])})"


def renc(line):
    """HL.enc of a script line (outputs outermost first, then the kernel)."""
    return [b[2] for b in line[0]], line[1]


def log_output_examples():
    """Scope table, row 'output of the new log n block below max(o, e)', and rows D10, D12.
    (1) [1,1,0,0] (p. A:36) at d = 1, a = x = 3/2, y = 0, c = 4/3: the printed speedup goes from (E n^0)^1
    DTISP[n^{3/2}, n^{3/2}] to (E n^{3/2})^{3/2} (A n^0)^1 DTISP[n^{3/2}, n^{3/2}], relaxed ([1], S 3/2 3/2) ->
    ([1, 3/2], S 3/2 3/2) in HL order. It is no single HL.RStep step (speedM needs the log n output >= 3/2), but
    it is RStep.slow to ([], T 2), RStep.convN (s = 1) to ([1], S 2 1) and RStep.speedM (x = 1/2) to the printed
    line. (2) From ([], S 1 1/2), HY.SpeedLog.new with x = 0 and log n output 1/2 (below max(HY.pin [], e) = 1)
    encodes to an HL.RStep.speedN step, since HL.pin [] = 0. (3) Case 1 (p. A:37) first speedup at the samples
    b = 4, e = 1 (printed output max(b, 1) = 4 >= max(b, e)): an HL.RStep step; b = 2, e = 3 (2 < 3): no HL.RStep
    step, an HL.Loose step."""
    d, a, x, y, c = 1, Q(3, 2), Q(3, 2), Q(0), Q(4, 3)
    L1 = conv(([], ("T", a)), x, d)
    printed = ([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))], ("S", a - y, d * x))
    src, dst = renc(L1), renc(printed)
    check(src == ([Q(1)], ("S", a, a)) and dst == ([Q(3, 2), Q(1)], ("S", a, a)), "A:36 a = x = 3/2: lines")
    check(not r_step_any(src, dst, c, d) and r_step_any(src, dst, c, d, loose=True),
          "A:36 a = x = 3/2: no single HL.RStep step (log n output 1 < 3/2); an HL.Loose step")
    m1, m2 = ([], ("T", Q(2))), ([Q(1)], ("S", Q(2), Q(1)))
    check(c * max(rpin([]), Q(1), a) <= 2, "expansion: RStep.slow to ([], T 2)")
    check(0 <= 1 <= 2 and max(rpin([]), 2 - 1) <= 1 and 2 <= 2 and d * 1 <= 1, "expansion: convN s = 1")
    xs = Q(1, 2)
    check(0 <= xs and 1 <= 2 - xs and max(Q(1), xs + 1) <= Q(3, 2) and max(Q(1), Q(1)) <= 1 and 2 - xs <= a
          and 1 <= a, "expansion: speedM x = 1/2")
    check(r_step_any(src, m1, c, d) and r_step_any(m1, m2, c, d) and r_step_any(m2, dst, c, d),
          "A:36 a = x = 3/2, c = 4/3: three relaxed steps")
    print(f"\n== p. A:36, [1,1,0,0] at d = 1, a = x = 3/2, y = 0, c = 4/3: the printed speedup {rshow(src)} ->"
          f" {rshow(dst)} is no single HL.RStep step (log n output 1 < max(1, 3/2)), an HL.Loose step;"
          f" RStep.slow to {rshow(m1)}, RStep.convN (s = 1) to {rshow(m2)}, RStep.speedM (x = 1/2) reach it (asserted)")
    sa, se, sx, sl = Q(1), Q(1, 2), Q(0), Q(1, 2)
    check(sa >= 1 and 0 <= se <= sa - sx and 0 <= sx <= sa - 1 and pin([]) >= 1 and sl >= 0,
          "SpeedLog.new from ([], S 1 1/2), x = 0: side conditions")
    sp = ([("E", sx + se, max(pin([]), sx + se)), ("A", Q(0), sl)], ("S", sa - sx, se))
    check(sp == ([("E", Q(1, 2), Q(1)), ("A", Q(0), Q(1, 2))], ("S", Q(1), Q(1, 2))), "SpeedLog.new line")
    check(Q(1, 2) < max(pin([]), Q(1, 2)) and r_step_any(([], ("S", Q(1), Q(1, 2))), renc(sp), c, d),
          "SpeedLog.new from ([], S 1 1/2) with x = 0, output 1/2: an RStep.speedN step")
    print(f"   HY.SpeedLog.new from ([], S 1 1/2), x = 0, log n output 1/2 < max(HY.pin [], e) = 1: encoding {rshow(renc(sp))},"
          " an HL.RStep.speedN step, since HL.pin [] = 0 (asserted)")
    for b, e, want in ((Q(4), Q(1), True), (Q(2), Q(3), False)):
        ap, a8, x1 = Q(2) if b == 4 else Q(1), Q(8), Q(2) if b == 4 else Q(1)
        start = P([("A", Q(0), b), ("E", ap, b)], ("S", a8, e))
        printed1 = P([("A", Q(0), b), ("E", max(ap, x1 + e), max(b, x1 + e)), ("A", Q(0), max(b, Q(1)))],
                     ("S", a8 - x1, e))
        y1 = Q(1)
        printed2 = P([("A", Q(0), b), ("E", max(ap, x1 + e), max(b, x1 + e)), ("A", y1, max(b, y1 + e, Q(1))),
                      ("E", Q(0), max(b, Q(1)))], ("S", a8 - x1 - y1, e))
        s0, s1, s2 = renc(start), renc(printed1), renc(printed2)
        check(r_step_any(s0, s1, Q(3, 2), 1) == want and r_step_any(s0, s1, Q(3, 2), 1, loose=True)
              and r_step_any(s1, s2, Q(3, 2), 1) == want and r_step_any(s1, s2, Q(3, 2), 1, loose=True),
              f"Case 1 sample b = {b}, e = {e}: printed speedups")
        print(f"   Case 1 sample b = {b}, e = {e}: each printed speedup (log n output max(b, 1) = {max(b, Q(1))};"
              f" the second with guess n^y) is"
              + (" an HL.RStep step" if want else " no HL.RStep step (needs >= max(b, e) = 3), an HL.Loose step")
              + " (asserted)")
    b, ap, a4, x1, y1, e = Q(1), Q(1), Q(4), Q(1), Q(1), Q(0)
    start = P([("A", Q(0), b), ("E", ap, b)], ("S", a4, e))
    printed1 = P([("A", Q(0), b), ("E", max(ap, x1 + e), max(b, x1 + e)), ("A", Q(0), max(b, Q(1)))],
                 ("S", a4 - x1, e))
    printed2 = P([("A", Q(0), b), ("E", max(ap, x1 + e), max(b, x1 + e)), ("A", y1, max(b, y1 + e, Q(1))),
                  ("E", Q(0), max(b, Q(1)))], ("S", a4 - x1 - y1, e))
    L1 = speed(start, x1)
    check(L1 == printed1 and speed(L1, y1) == printed2,
          "Case 1 at e = 0: both printed speedups are HY.Step.speedMerge steps")
    print(f"   Case 1 at d = 1, a = 4, b = a' = 1, x = y = 1, e = 0: the printed guess n^y equals Lemma 3.3's n^(y+e),"
          f" and both printed speedups, {show(printed1)} and {show(printed2)}, are HY.Step.speedMerge steps with the"
          " printed guesses and outputs (asserted)")



def d17_output_example():
    """Rows D17 and item 3: [1,1,0,0] (p. A:36) at d = 1, a = 3, x = 1/4, y = 5/2 violates y <= a - 1 while
    dx <= a - y. The Lemma 7.1 line is (E n^{11/4})^{11/4} DTISP[n^3, n^{1/4}]; the printed speedup gives the new
    log n block the output 1 < max(11/4, 1/4), so it is no HL.RStep step (speedM is the only constructor of that
    shape), but an HL.Loose step."""
    d, a, x, y, c = 1, Q(3), Q(1, 4), Q(5, 2), Q(3, 2)
    L1 = conv(([], ("T", a)), x, d)
    printed = ([("E", max(a - x, y + d * x), max(a - x, y + d * x, Q(1))), ("A", Q(0), Q(1))], ("S", a - y, d * x))
    try:
        speed(L1, y)
        exact = True
    except RuleError:
        exact = False
    src, dst = renc(L1), renc(printed)
    check(L1 == ([("E", Q(11, 4), Q(11, 4))], ("S", a, Q(1, 4))) and y > a - 1 and d * x <= a - y and not exact,
          "D17 a = 3: Lemma 7.1 line, y > a - 1, dx <= a - y, no HY.Step speedup")
    check(dst == ([Q(11, 4), Q(1)], ("S", Q(1, 2), Q(1, 4))) and not r_step_any(src, dst, c, d)
          and r_step_any(src, dst, c, d, loose=True), "D17 a = 3: no HL.RStep step, an HL.Loose step")
    print(f"\n== p. A:36, [1,1,0,0] at d = 1, a = 3, x = 1/4, y = 5/2: y > a - 1, dx <= a - y; from {show(L1)} the"
          f" display gives {show(printed)}: log n output 1 < 11/4, so no HL.RStep step; an HL.Loose step (asserted)")


def thm79_case1_31():
    """Inequality (31) of the sketch of Theorem 7.9, Case 1 (pp. A:37-A:38), max{b, 1, x+e, a-x} <=
    c max{b, y+e, 1, x+e, a-x-y}, at d = 1, c = 3/2 = (d+2)/(d+1), b = a' = 1, a = 5, e = 1/2, x = 0, y = 9/4,
    which satisfy the side conditions of both Lemma 3.3 steps of Case 1 (HY.Step's speedMerge conditions:
    a >= 1, 0 <= e <= a-x, 0 <= x <= a-1, then the same for a-x and y)."""
    d, c, b, ap, a, e, x, y = 1, Q(3, 2), Q(1), Q(1), Q(5), Q(1, 2), Q(0), Q(9, 4)
    check(c >= Q(d + 2, d + 1), "(31) sample: c >= (d+2)/(d+1)")
    line = P([("A", Q(0), b), ("E", ap, b)], ("S", a, e))
    L1 = speed(line, x)
    L2 = speed(L1, y)
    lhs = max(b, Q(1), x + e, a - x)
    rhs = c * max(b, y + e, Q(1), x + e, a - x - y)
    check(lhs == 5 and rhs == Q(33, 8) and lhs > rhs, "(31) fails at the sample")
    print(f"\n== p. A:37, inequality (31) at d = {d}, c = {c}, b = a' = {b}, a = {a}, e = {e}, x = {x}, y = {y}: both"
          f" Lemma 3.3 steps apply ({show(L2)}); (31) reads {lhs} <= {rhs}, which is false (asserted)")


def section52_example():
    """Paper Section 5.2: an S-level closed below c max(top, space) by one Lemma 7.2 step (d = 2, c = 3/2)."""
    d, c = 2, Q(3, 2)
    L1 = conv(([], ("T", Q(1))), Q(1), d)
    L2 = slow(L1, c)
    top, (_, a, e) = L1[0][-1][2], L1[1]
    psS = min(max(top, a), c * max(top, e))
    check(L1 == ([("E", Q(0), Q(1))], ("S", Q(1), Q(2))) and L2 == ([], ("T", c)) and c < c * max(top, e)
          and c * psS == c, "Section 5.2 example")
    print(f"\n== Paper Section 5.2: DTIME_2[n^1], Lemma 7.1 (s = 1) gives {show(L1)}, Lemma 7.2 gives {show(L2)};"
          f" c max(top, space) = {c * max(top, e)}; psi_S(1, 1, 2) = {psS} (asserted)")


def section24_example():
    """Paper Section 2.4, item 3: d = 1, DTIME_1[n^4], Lemma 7.1 (s = 3), Lemma 3.3 (x = 0)."""
    L1 = conv(([], ("T", Q(4))), Q(3), 1)
    L2 = speed(L1, Q(0))
    check(L1 == ([("E", Q(1), Q(1))], ("S", Q(4), Q(3))) and L2[0][-1][2] == 3, "Section 2.4 example")
    print(f"\n== Paper Section 2.4, item 3: DTIME_1[n^4], Lemma 7.1 (s = 3) gives {show(L1)}, Lemma 3.3 (x = 0) gives"
          f" {show(L2)}: the new log n block gets max(1, 3) = 3 (asserted)")


def main():
    section24_example()
    section52_example()
    example_a31()
    lemma77()
    theorem75()
    cor78_base_printed()
    thm79_1100()
    thm79_1100_side()
    thm79_010()
    thm79_case1()
    thm79_case2()
    thm79_case1_31()
    slow_relaxed_test()
    expansion_example()
    speed_outside_a36()
    log_output_examples()
    d17_output_example()
    print("\n== Summary: transitions whose output differs from the printed line, the rule applied to the printed"
          " previous line (omitted superscripts read block-wise)")
    for title, ell, rows in SUMMARY:
        bad = [f"{label}: {'; '.join(dp)}" for label, dp in rows if dp]
        print(f"   {title} [l = {ELL[ell][0]}]: " + ("all agree" if not bad else " | ".join(bad)))
    print("\n== Kernels of the replays from our own previous line, compared across the outputs l under which a display"
          " is replayed")
    for key, runs in KERNELS.items():
        if len(runs) > 1:
            same = all(k == runs[0][1] for _, k in runs)
            check(same, f"kernels differ across outputs for {key}")
            name = key if isinstance(key, str) else key[0] + " (" + ", ".join(str(v) for v in key[1:]) + ")"
            print(f"   {name}: outputs {', '.join(ELL[e][0] for e, _ in runs)}: every kernel the same (asserted)")
    print(f"\n{CHECKS[0]} assertions hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
