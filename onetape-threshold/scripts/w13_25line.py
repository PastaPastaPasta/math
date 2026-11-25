#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Calibration: replays the 25-line proof printed in Williams's TOCT paper (Section 7.2, pp. A:32-A:33;
d = 1) under the rules of the formal calculus HY.Step (merged Lemma 7.1, merged Lemma 3.3 inside a prefix,
Lemma 7.2), with c = 1.297844 (the value implied by its lines 9 -> 10).

The printed lines show each block's guess exponent, log n blocks as n^1, and no output superscripts. The
script carries the full state (quantifier, guess, output superscript) itself: for each printed step it
infers the rule from the shape of the next line and its parameter from the printed numbers (s from the new
space exponent, x from the new time exponent), applies the rule exactly, and compares every printed
number with the computed one (block exponents as max(guess, 1)). It reports the largest deviation; the
printed numbers have 9-10 significant digits.

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


def main():
    c, d = Q("1.297844"), 1
    printed = [parse(l) for l in PRINTED.strip().split("\n")]
    state = ([], printed[0][1])
    worst = Q(0)
    rules = []
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
            ker = ("S", a, d * s); rules.append("L7.1")
        elif ker[0] == "S" and len(pb) == len(blocks) + 1:
            a, e = ker[1], ker[2]
            x = a - pk[1]
            assert a >= 1 and 0 <= e <= a - x and 0 <= x <= a - 1 and b >= 1
            q, g, o = blocks[-1]
            blocks = blocks[:-1] + [(q, max(g, x + e), max(o, x + e)), ("A" if q == "E" else "E", Q(0), max(o, e))]
            ker = ("S", a - x, e); rules.append("L3.3")
        elif len(pb) == len(blocks) - 1:
            q, g, o = blocks[-1]
            bk = blocks[-2][2] if len(blocks) > 1 else Q(1)
            assert bk >= 1 and o >= 1 and ker[1] >= 1 and g >= 0
            blocks = blocks[:-1]
            ker = ("T", c * max(bk, o, g, ker[1])); rules.append("L7.2")
        else:
            raise SystemExit(f"line {k}: no rule matches")
        assert [q for q, *_ in blocks] == [q for q, _ in pb], f"line {k}: quantifiers"
        assert all(blocks[i][0] != blocks[i + 1][0] for i in range(len(blocks) - 1)), f"line {k}: alternation"
        devs = [abs(max(g, 1) - pg) for (q, g, o), (_, pg) in zip(blocks, pb)]
        devs += [abs(x - y) for x, y in zip(ker[1:], pk[1:])]
        assert ker[0] == pk[0]
        worst = max(worst, max(devs))
        state = (blocks, ker)
    final, start = state[1][1], printed[0][1][1]
    print(f"rules: {' '.join(rules)}")
    print(f"every step is a rule of the formal calculus; largest deviation from the printed numbers: {float(worst):.2e}")
    print(f"computed final exponent {float(final):.10f} vs. start {float(start):.10f} (difference {float(final - start):.2e})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
