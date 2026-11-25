#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Calibration: replays the 25-line proof printed in Williams's TOCT paper (Section 7.2, pp. A:32-A:33;
d = 1) under the rules of the formal calculus HY.Step (Lemma 7.1, Lemma 3.3 merged inside a prefix,
Lemma 7.2), with c = 1.297844 (the value implied by its lines 9 -> 10).

The printed lines show each block's guess exponent, log n blocks as n^1, and no output superscripts. The
script carries the full state (quantifier, guess, output superscript) itself: for each printed step it
infers the rule from the shape of the next line and its parameter from the printed numbers (s from the new
space exponent, x from the new time exponent), applies the rule exactly, and compares every printed
number with the computed one. Compared are the kernel exponents (time, and space on DTISP lines),
directly, and the block guess exponents, as max(guess, 1), since the printed lines show guesses below 1
(log n blocks, and the first block, whose computed guess is 0.999997582) as n^1. Output superscripts are
not printed, so they are not compared. It reports the largest deviations, per transition and overall,
the blocks whose printed guess is below the previous line's (no merged rule lowers a guess), and whether
the computed last line agrees with the printed one in the last printed digit (it does not: 1.7519584642
rounds to 1.751958464, Williams prints 1.751958454).

The replay is run with four outputs for the new log n block of Lemma 3.3: max(b, e) of HY.Step, exactly 1,
max(b, 1) (the display of Case 1 of the sketch of Theorem 7.9) and max(1, e). All reproduce every printed
number to the same precision, so the display does not decide between them. For each, the script lists the
Lemma 7.2 steps at which the output superscript of the remaining prefix (b_k) is the strict maximum, i.e.
where a slowdown maximum without b_k (as displayed on p. A:36) would give a smaller exponent: none under
max(b, e). It also compares the carried output superscripts with Williams's default for an omitted
superscript (Section 2, p. A:5), read block-wise (the output of a block of guess a_i is max{a_i, 1}, so 1
for a log n block): under max(b, e) the log n blocks of lines 13, 16, 19 and 22 get about 1.04010891
(inherited from the enclosing existential block), not the default 1. The next step removes each of them by
Lemma 7.2, whose maximum contains that existential block's output, so no printed number depends on the
difference.

This is a replay of Williams's rounded display, not a verified proof: replayed from the printed start
1.751958454 at c = 1.297844, the computed last line is about 1.0e-8 above the first, so the normal-form
condition a' < a fails at that c. The script reports this.

usage: w13_25line.py      (Python 3 standard library only; exact arithmetic except for the comparison)"""
import re
import sys
from fractions import Fraction as Q

PRINTED = """
0, DTIME1[n^1.751958454]
1, (E n^1.)DTISP[n^1.751958454,n^.7519608720]
2, (E n^1.040108911)(A n^1.)DTISP[n^1.463810415,n^.7519608720]
3, (E n^1.040108911)(A n^1.)(E n^1.)DTISP[n^1.215771287,n^.7519608720]
4, (E n^1.040108911)(A n^1.)DTIME1[n^1.577881470]
5, (E n^1.040108911)(A n^1.)DTISP[n^1.577881470,n^.5778814720]
6, (E n^1.040108911)(A n^1.)(E n^1.)DTISP[n^1.155762944,n^.5778814720]
7, (E n^1.040108911)(A n^1.)DTIME1[n^1.5]
8, (E n^1.040108911)(A n^1.)DTISP[n^1.5,n^.5]
9, (E n^1.040108911)(A n^1.)(E n^1.)DTISP[n^1.,n^.5]
10, (E n^1.040108911)(A n^1.)DTIME1[n^1.297844000]
11, (E n^1.040108911)DTIME1[n^1.684399048]
12, (E n^1.040108909)DTISP[n^1.684399048,n^.6442901394]
13, (E n^1.040108909)(A n^1.)DTISP[n^1.288580278,n^.6442901394]
14, (E n^1.040108909)DTIME1[n^1.672376183]
15, (E n^1.040108909)DTISP[n^1.672376183,n^.6322672739]
16, (E n^1.040108909)(A n^1.)DTISP[n^1.264534548,n^.6322672739]
17, (E n^1.040108909)DTIME1[n^1.641168576]
18, (E n^1.040108909)DTISP[n^1.641168576,n^.6010596669]
19, (E n^1.040108911)(A n^1.)DTISP[n^1.202119332,n^.6010596669]
20, (E n^1.040108911)DTIME1[n^1.560163362]
21, (E n^1.040108911)DTISP[n^1.560163362,n^.5200544533]
22, (E n^1.040108908)(A n^1.)DTISP[n^1.040108908,n^.5200544533]
23, (E n^1.040108908)DTIME1[n^1.349899105]
24, DTIME1[n^1.751958454]
"""


def parse(line):
    i, rest = line.split(", ", 1)
    blocks = [(q, Q(g)) for q, g in re.findall(r"\((E|A) n\^([0-9.]+)\)", rest)]
    m = re.search(r"DTIME1\[n\^([0-9.]+)\]", rest)
    if m:
        return blocks, ("T", Q(m.group(1)))
    m = re.search(r"DTISP\[n\^([0-9.]+),n\^([0-9.]+)\]", rest)
    return blocks, ("S", Q(m.group(1)), Q(m.group(2)))


ELL = {
    "max": ("max(b, e) (HY.Step)", lambda o, e: max(o, e)),
    "one": ("exactly 1", lambda o, e: Q(1)),
    "in": ("max(b, 1) (the display of Case 1, p. A:37)", lambda o, e: max(o, Q(1))),
    "sp": ("max(1, e)", lambda o, e: max(Q(1), e)),
}


def replay(printed, c, d, ell):
    state = ([], printed[0][1])
    worst_k = Q(0)
    worst_g = Q(0)
    raw_g = []
    rules = []
    states = [state]
    bk_max = []
    per = []
    for k in range(1, len(printed)):
        blocks, ker = state
        pb, pk = printed[k]
        b = blocks[-1][2] if blocks else Q(1)
        if ker[0] == "T" and pk[0] == "S":
            s = pk[2] / d
            a = ker[1]
            assert 0 < s <= a and b >= 1
            if blocks:
                q, g, o = blocks[-1]
                blocks = blocks[:-1] + [(q, max(g, a - s), max(a - s, o))]
            else:
                blocks = [("E", a - s, max(a - s, b))]
            ker = ("S", a, d * s); rules.append("L7.1"); par = ("s", s)
        elif ker[0] == "S" and len(pb) == len(blocks) + 1:
            a, e = ker[1], ker[2]
            x = a - pk[1]
            assert a >= 1 and 0 <= e <= a - x and 0 <= x <= a - 1 and b >= 1
            q, g, o = blocks[-1]
            lo = ELL[ell][1](o, e)
            blocks = blocks[:-1] + [(q, max(g, x + e), max(o, x + e)), ("A" if q == "E" else "E", Q(0), lo)]
            ker = ("S", a - x, e); rules.append("L3.3"); par = ("x", x)
        elif len(pb) == len(blocks) - 1:
            q, g, o = blocks[-1]
            bk = blocks[-2][2] if len(blocks) > 1 else Q(1)
            assert bk >= 1 and o >= 1 and ker[1] >= 1 and g >= 0
            if bk > max(o, g, ker[1]):
                bk_max.append((k, bk - max(o, g, ker[1])))
            blocks = blocks[:-1]
            ker = ("T", c * max(bk, o, g, ker[1])); rules.append("L7.2"); par = None
        else:
            raise SystemExit(f"line {k}: no rule matches")
        assert [q for q, *_ in blocks] == [q for q, _ in pb], f"line {k}: quantifiers"
        assert all(blocks[i][0] != blocks[i + 1][0] for i in range(len(blocks) - 1)), f"line {k}: alternation"
        assert ker[0] == pk[0]
        gd = max([Q(0)] + [abs(max(g, 1) - pg) for (q, g, o), (_, pg) in zip(blocks, pb)])
        kd = max(abs(x - y) for x, y in zip(ker[1:], pk[1:]))
        prev_pb = printed[k - 1][0]
        lower = [i + 1 for i in range(min(len(pb), len(prev_pb))) if pb[i][1] < prev_pb[i][1]]
        per.append((k, rules[-1], par, kd, gd, lower))
        worst_g = max(worst_g, gd)
        worst_k = max(worst_k, kd)
        raw_g += [(k, g, pg) for (q, g, o), (_, pg) in zip(blocks, pb) if 0 < g < 1]
        state = (blocks, ker)
        states.append(state)
    return rules, states, worst_k, worst_g, raw_g, bk_max, per


def main():
    c, d = Q("1.297844"), 1
    printed = [parse(l) for l in PRINTED.strip().split("\n")]
    start = printed[0][1][1]
    ref = None
    for ell in ("max", "one", "in", "sp"):
        rules, states, worst_k, worst_g, raw_g, bk_max, per = replay(printed, c, d, ell)
        final = states[-1][1][1]
        print(f"new log n block of Lemma 3.3 with output {ELL[ell][0]}:")
        if ref is None:
            ref = states
            print(f"  rules: {' '.join(rules)}")
            print("  every step is a rule of the formal calculus with its side conditions")
            print("  compared: kernel exponents (time, and space on DTISP lines) and max(guess, 1) for every block;"
                  " output superscripts are not printed")
        else:
            kdiff = [k for k in range(len(states)) if states[k][1] != ref[k][1]]
            print("  every step is a rule of this variant with its side conditions; kernels that differ from the"
                  f" max(b, e) replay: {kdiff if kdiff else 'none'}")
        print(f"  largest deviation of a kernel exponent from the printed number: {float(worst_k):.3e}")
        print(f"  largest deviation of max(guess, 1) from the printed block exponent: {float(worst_g):.2e}")
        for k, g, pg in raw_g[:1]:
            print(f"    (line {k}: computed guess {float(g):.9f}, printed n^{float(pg):g})")
        last = round(final, 9)
        print(f"  computed final exponent {float(final):.10f}, printed {float(start):.9f}: difference"
              f" {float(final - start):.3e}; rounded to the printed 9 decimals it is {float(last):.9f}, so the"
              + (" last printed digit agrees" if last == start else " last printed digit does not agree"))
        if final >= start:
            print("  the computed last line is not below the first: at c = 1.297844 this replay of the rounded display"
                  " is not a strict normal-form proof (a' < a fails)")
        print("  slowdowns at which the output superscript of the remaining prefix (b_k of Lemma 7.2) is the strict"
              " maximum: " + (", ".join(f"line {k} (by {float(m):.2e})" for k, m in bk_max) if bk_max else "none"))
        if ell == "max":
            print("  per transition (to line k): rule, parameter, largest deviation of a kernel exponent and of"
                  " max(guess, 1) from the printed numbers, and the blocks whose printed guess is below the previous"
                  " line's (no merged rule lowers a guess):")
            for k, r, par, kd, gd, lower in per:
                ps = f"{par[0]} = {float(par[1]):.10f}" if par else "-"
                print(f"    {k:2d} {r} {ps:16s} kernel {float(kd):.2e}  guess {float(gd):.2e}"
                      + (f"  printed guess lowered in block {lower}" if lower else ""))
            dev = []
            for k, (blocks, ker) in enumerate(states):
                for i, (q, g, o) in enumerate(blocks):
                    default = max(g, Q(1))
                    if abs(o - default) > Q(1, 10**7):
                        dev.append((k, i, q, g, o, default))
            print("  carried output superscripts that differ by more than 1e-7 from Williams's default for an omitted"
                  " superscript, read block-wise (the output of a block of guess a_i is max{a_i, 1}, p. A:5):")
            for k, i, q, g, o, default in dev:
                kind = "log n" if g == 0 else f"n^{float(g):.9f}"
                print(f"    line {k}, block {i + 1} ({q} {kind}): output {float(o):.9f}, default {float(default):.9f}")
    print("every reading reproduces every printed number to within the same deviations: the display does not decide"
          " between them")
    return 0


if __name__ == "__main__":
    sys.exit(main())
