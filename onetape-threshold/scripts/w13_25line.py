#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Calibration: replays the 25-line proof printed in Williams's TOCT paper (Section 7.2, pp. A:32-A:33;
d = 1) under the rules of the formal calculus HY.Step (Lemma 7.1, Lemma 3.3 merged inside a prefix,
Lemma 7.2), with c = 1.297844 (the value implied by its lines 9 -> 10).

The printed lines show each block's guess exponent, log n blocks as n^1, and no output superscripts. The
script carries the full state (quantifier, guess, output superscript) itself: for each printed step it
infers the rule from the shape of the next line and its parameter from the printed numbers (s from the new
space exponent, x from the new time exponent), applies the rule exactly, and compares every printed
number with the computed one. The rule is applied to the computed previous line, not to the printed one, so
the deviations accumulate along the replay. Compared are the kernel exponents (time, and space on DTISP lines),
directly, and the block guess exponents, as max(guess, 1), since the printed lines show guesses below 1
(log n blocks, and the first block, whose computed guess is 0.999997582) as n^1. Output superscripts are
not printed, so they are not compared. It reports the largest deviations, per transition and overall,
the blocks whose printed guess is below the previous line's (no merged rule lowers a guess), and compares
the computed last line with the printed one rounded to nine decimal places (1.7519584642 rounds to
1.751958464, Williams prints 1.751958454: they differ in the eighth decimal place; asserted).

The replay is run with four outputs for the new log n block of Lemma 3.3: max(b, e) of HY.Step, exactly 1,
max(b, 1) (the display of Case 1 of the sketch of Theorem 7.9) and max(1, e). All reproduce every printed
number to the same precision, with the same kernels (asserted), so the display does not decide between
them. For each, the script lists the
Lemma 7.2 steps at which the output superscript of the remaining prefix (b_k) is the strict maximum, i.e.
where a slowdown maximum without b_k (as displayed on p. A:36) would give a smaller exponent: none under
max(b, e). It also compares the carried output superscripts with Williams's default for an omitted
superscript (Section 2, p. A:5), read block-wise (the output of a block of guess a_i is max{a_i, 1}, so 1
for a log n block): under max(b, e) the log n blocks of lines 13, 16, 19 and 22 get about 1.04010891
(inherited from the enclosing existential block), not the default 1. The next step removes each of them by
Lemma 7.2, whose maximum contains that existential block's output, so no printed number depends on the
difference.

This is a replay of Williams's printed display, not a verified proof: replayed from the printed start
1.751958454 at c = 1.297844, the computed last line is about 1.0e-8 above the first, so the normal-form
condition a' < a fails at that c. The script reports this.

It also reads every printed transition literally against the relaxed calculus HL.RStep (omitted outputs
read block-wise, printed kernels; function literal) and asserts which transitions no relaxed rule reproduces:
the slowdowns to lines 4, 7, 11, 20, 23, 24 print a time below c max(pin rest, b, time k) (line 6 -> 7:
c * 1.155762944 = 1.500000002292736 > 1.5), the existential output falls at lines 12 (1.040108911 ->
1.040108909, convM) and 22 (-> 1.040108908, speedM), lines 13, 15, 18 fail the relaxed conditions on a - s or x, and
the log n blocks of lines 13, 16, 19, 22 have the default output 1 below max(b, e) (row D3). Apart from the
last, every such failure is by at most 3e-9. The numerical origin of these discrepancies is not determined; the
comparison uses the exact replay in place of the printed numbers.

At c = 1.29784399 the same replay (same rules, parameters read off the printed lines) passes every side
condition and ends at 1.751958432856..., strictly below its start 1.751958454 (asserted).

Row D3: the printed Lemma 3.3 transitions to lines 13, 16, 19, 22, read literally with any log n output >= 0
allowed (HY.SpeedLog, relaxed HL.Loose): lines 16 and 19 are HL.Loose steps, 13 (no admissible x) and 22
(existential output lowered) are not; line 16 is an exact HY.SpeedLog step, line 19 is not (x = 0.439049244
gives the merged guess 1.0401089109 against the printed 1.040108911). Asserted, as are every value the paper
quotes from this script: the largest deviations, the first guess, the final exponent, the b_k rows under each
output, the blocks whose printed guess drops, the carried log n outputs and the body of the A.2 table.

With --tex it also prints the body of the table of Appendix A.2 of the paper (rule and largest deviations
per transition, and the notes D1-D3), from which that table is copied.

usage: w13_25line.py [--tex]      (Python 3 standard library only; exact arithmetic except for the comparison)"""
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


def literal(printed, c, d):
    """Each printed transition, read literally, against the relaxed calculus HL.RStep (Relaxed.lean), which
    bounds every output, time and space only from below and has no guesses. A printed line is encoded with
    Williams's default for omitted superscripts read block-wise (the output of a block is max{guess, 1}; the
    printed n^1 of a log n block gives 1) and its printed kernel. For each transition the conditions of the
    matching constructor are tested with the best choice of its parameter (convM/convN: s = min(a, e/d);
    speedM: any x in [max(0, a - a2), min(a - e, b' - e)]; slow: c max(pin rest, b, time k) <= a'). Returns,
    per transition, the failed conditions as (kind, amount); kind is "slow" (printed time below the relaxed
    lower bound), "lowered" (printed output of the innermost block below the old one, which convM and speedM
    forbid), "log" (printed log n output 1 below max(b, e)) or "other" (convM a - s, or speedM no x)."""
    def enc(line):
        blocks, ker = line
        return [max(g, Q(1)) for _, g in blocks], ker

    def rpin(outs):
        return outs[-1] if outs else Q(0)

    res = {}
    for k in range(1, len(printed)):
        (o0, k0), (o1, k1) = enc(printed[k - 1]), enc(printed[k])
        bad = []
        if k0[0] == "T" and k1[0] == "S":
            a, a2, e = k0[1], k1[1], k1[2]
            s = min(a, e / d)
            if len(o1) == len(o0):
                assert o1[:-1] == o0[:-1] and a <= a2
                b, b1 = o0[-1], o1[-1]
                if b1 < b:
                    bad.append(("lowered", b - b1))
                if b1 < a - s:
                    bad.append(("other", a - s - b1))
            else:
                assert o1[:-1] == o0 and a <= a2 and max(rpin(o0), a - s) <= o1[-1]
        elif k0[0] == "S" and len(o1) == len(o0) + 1:
            a, e, a2, e2 = k0[1], k0[2], k1[1], k1[2]
            b, bp, L = o0[-1], o1[-2], o1[-1]
            assert o1[:-2] == o0[:-1] and e <= e2
            lo, hi = max(Q(0), a - a2), min(a - e, bp - e)
            if hi < lo:
                bad.append(("other", lo - hi))
            if bp < b:
                bad.append(("lowered", b - bp))
            if L < max(b, e):
                bad.append(("log", max(b, e) - L))
        else:
            assert len(o1) == len(o0) - 1 and o1 == o0[:-1]
            lb = c * max(rpin(o0[:-1]), o0[-1], k0[1])
            if k1[1] < lb:
                bad.append(("slow", lb - k1[1]))
        res[k] = bad
    return res


def d3_literal(printed, d):
    """Row D3, the printed Lemma 3.3 transitions to lines 13, 16, 19 and 22 read literally with the log n output
    allowed to be any value >= 0 (HY.SpeedLog, relaxed form HL.Loose), omitted outputs read block-wise. Returns,
    per line, the parameter x fixed by the printed times, the merged guess max(g, x + e) that Lemma 3.3 gives from
    the printed previous line, the printed guess, whether the printed line is an exact HY.SpeedLog step (side
    conditions, merged guess and output, kernel; the printed n^1 of the new block read as a log n guess) and
    whether its encoding is an HL.Loose.speedM step (some x in [max(0, a - a2), min(a - e, b' - e)] and the outer
    output not lowered)."""
    res = {}
    for k in (13, 16, 19, 22):
        (pb, pk), (nb, nk) = printed[k - 1], printed[k]
        a, e = pk[1], pk[2]
        x = a - nk[1]
        g = pb[-1][1]
        o = max(g, Q(1))
        mg = max(g, x + e)
        pg = nb[-2][1]
        side = a >= 1 and 0 <= e <= a - x and 0 <= x <= a - 1 and o >= 1 and nk[2] == e
        exact = side and mg == pg and max(o, x + e) == max(pg, Q(1)) and [q for q, _ in nb[:-1]] == [q for q, _ in pb]
        bp = max(pg, Q(1))
        lo, hi = max(Q(0), a - nk[1]), min(a - e, bp - e)
        loose = lo <= hi and o <= bp and e <= nk[2]
        res[k] = (x, mg, pg, exact, loose)
    return res


EXPECTED_TEX = [
    r"1 & L7.1 & 0 & 0 (first guess $0.999997582$) & 13 & L3.3 & 0 & $4.6\cdot10^{-9}$; D3\\",
    r"2 & L3.3 & 0 & 0 & 14 & L7.2 & $6.8\cdot10^{-10}$ & $4.6\cdot10^{-9}$\\",
    r"3 & L3.3 & 0 & 0 & 15 & L7.1 & $6.8\cdot10^{-10}$ & $4.6\cdot10^{-9}$\\",
    r"4 & L7.2 & $2.1\cdot10^{-10}$ & 0 & 16 & L3.3 & 0 & $4.6\cdot10^{-9}$; D3\\",
    r"5 & L7.1 & $2.1\cdot10^{-10}$ & 0 & 17 & L7.2 & $8.5\cdot10^{-11}$ & $4.6\cdot10^{-9}$\\",
    r"6 & L3.3 & 0 & 0 & 18 & L7.1 & $8.5\cdot10^{-11}$ & $4.6\cdot10^{-9}$\\",
    r"7 & L7.2 & $2.3\cdot10^{-9}$ & 0 & 19 & L3.3 & 0 & $2.6\cdot10^{-9}$; D3\\",
    r"8 & L7.1 & $2.3\cdot10^{-9}$ & $2.3\cdot10^{-9}$ & 20 & L7.2 & $3.2\cdot10^{-10}$ & $2.6\cdot10^{-9}$\\",
    r"9 & L3.3 & 0 & $2.3\cdot10^{-9}$ & 21 & L7.1 & $3.2\cdot10^{-10}$ & $2.6\cdot10^{-9}$\\",
    r"10 & L7.2 & $3.0\cdot10^{-9}$ & $2.3\cdot10^{-9}$ & 22 & L3.3 & 0 & $5.6\cdot10^{-9}$; D2, D3\\",
    r"11 & L7.2 & $4.2\cdot10^{-9}$ & 0 & 23 & L7.2 & $7.9\cdot10^{-9}$ & $5.6\cdot10^{-9}$\\",
    r"12 & L7.1 & $4.2\cdot10^{-9}$ & $3.8\cdot10^{-9}$; D2 & 24 & L7.2 & $1.023\cdot10^{-8}$ & 0; D1\\",
]


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
            ref_dev = (worst_k, worst_g)
            print(f"  rules: {' '.join(rules)}")
            print("  every step of the exact replay satisfies the formal rules, side conditions included")
            print("  compared: kernel exponents (time, and space on DTISP lines) and max(guess, 1) for every block;"
                  " output superscripts are not printed")
        else:
            kdiff = [k for k in range(len(states)) if states[k][1] != ref[k][1]]
            assert not kdiff, f"kernels differ from the max(b, e) replay at lines {kdiff}"
            assert (worst_k, worst_g) == ref_dev, "deviations differ from the max(b, e) replay"
            print("  every step of the exact replay satisfies this variant's rules, side conditions included; kernels"
                  " that differ from the"
                  " max(b, e) replay: none (asserted)")
        assert f"{float(worst_k):.7e}" == "1.0230064e-08" and worst_k < Q(103, 10**10), worst_k
        assert f"{float(worst_g):.2e}" == "5.60e-09" and worst_g < Q(6, 10**9), worst_g
        assert raw_g[0][0] == 1 and f"{float(raw_g[0][1]):.9f}" == "0.999997582", raw_g[0]
        assert f"{float(final):.10f}" == "1.7519584642", final
        if ell in ("max", "in"):
            assert bk_max == [], bk_max
        else:
            assert [k for k, _ in bk_max] == [10, 23] and all(0 < m < Q(6, 10**9) for _, m in bk_max), bk_max
        print(f"  largest deviation of a kernel exponent from the printed number: {float(worst_k):.7e} (asserted)")
        print(f"  largest deviation of max(guess, 1) from the printed block exponent: {float(worst_g):.2e} (asserted)")
        for k, g, pg in raw_g[:1]:
            print(f"    (line {k}: computed guess {float(g):.9f}, printed n^{float(pg):g}; asserted)")
        last = round(final, 9)
        diffpos = next((i + 1 for i, (u, v) in enumerate(zip(f"{float(last):.9f}".split(".")[1],
                                                               f"{float(start):.9f}".split(".")[1])) if u != v), None)
        assert diffpos == 8, diffpos
        print(f"  computed final exponent {float(final):.10f}, printed {float(start):.9f}: difference"
              f" {float(final - start):.7e}; rounded to nine decimal places it is {float(last):.9f}, so the two"
              " differ when rounded to nine decimal places, first in the eighth decimal place")
        if final >= start:
            print("  the computed last line is not below the first: at c = 1.297844 this replay of the printed display"
                  " is not a strict normal-form proof (a' < a fails)")
        print("  slowdowns at which the output superscript of the remaining prefix (b_k of Lemma 7.2) is the strict"
              " maximum: " + (", ".join(f"line {k} (by {float(m):.2e})" for k, m in bk_max) if bk_max else "none"))
        if ell == "max":
            tex_rows = table_rows(per, raw_g, states, worst_k)
            assert tex_rows == EXPECTED_TEX, tex_rows
            assert {k: lower for k, _, _, _, _, lower in per if lower} == {12: [1], 22: [1]}
            for k in (12, 22):
                gap = states[k][0][0][1] - printed[k][0][0][1]
                assert 0 < gap < Q(6, 10**9), (k, gap)
            print("  per transition (to line k): rule, parameter, largest deviation of a kernel exponent and of"
                  " max(guess, 1) from the printed numbers, and the blocks whose printed guess is below the previous"
                  " line's (no merged rule lowers a guess):")
            for k, r, par, kd, gd, lower in per:
                ps = f"{par[0]} = {float(par[1]):.10f}" if par else "-"
                print(f"    {k:2d} {r} {ps:16s} kernel {float(kd):.3e}  guess {float(gd):.3e}"
                      + (f"  printed guess lowered in block {lower}" if lower else ""))
            dev = []
            for k, (blocks, ker) in enumerate(states):
                for i, (q, g, o) in enumerate(blocks):
                    default = max(g, Q(1))
                    if abs(o - default) > Q(1, 10**7):
                        dev.append((k, i, q, g, o, default))
            assert sorted({k for k, i, q, g, o, default in dev if g == 0}) == [13, 16, 19, 22] and all(
                g == 0 and f"{float(o):.8f}" == "1.04010891" and default == 1
                for k, i, q, g, o, default in dev), dev
            print("  carried output superscripts that differ by more than 1e-7 from Williams's default for an omitted"
                  " superscript, read block-wise (the output of a block of guess a_i is max{a_i, 1}, p. A:5):")
            for k, i, q, g, o, default in dev:
                kind = "log n" if g == 0 else f"n^{float(g):.9f}"
                print(f"    line {k}, block {i + 1} ({q} {kind}): output {float(o):.9f}, default {float(default):.9f}")
    print("every reading reproduces every printed number to within the same deviations (asserted): the display does"
          " not decide between them")
    lit = literal(printed, c, d)
    kinds = {kind: sorted(k for k, bad in lit.items() if any(b[0] == kind for b in bad))
             for kind in ("slow", "lowered", "log", "other")}
    assert kinds == {"slow": [4, 7, 11, 20, 23, 24], "lowered": [12, 22], "log": [13, 16, 19, 22],
                     "other": [13, 15, 18]}, kinds
    lb7 = c * printed[6][1][1]
    assert printed[6][1][1] == Q("1.155762944") and printed[7][1][1] == Q("1.5")
    assert lb7 == Q("1.500000002292736") and ("slow", lb7 - Q("1.5")) in lit[7]
    assert printed[11][0][0][1] == Q("1.040108911") and printed[12][0][0][1] == Q("1.040108909")
    assert ("lowered", Q("0.000000002")) in lit[12] and ("lowered", Q("0.000000003")) in lit[22]
    gaps = [amt for bad in lit.values() for kind, amt in bad if kind != "log"]
    assert max(gaps) == Q("0.000000003")
    ok = [k for k, bad in lit.items() if not bad]
    assert ok == [1, 2, 3, 5, 6, 8, 9, 10, 14, 17, 21], ok
    print("the printed transitions read literally (omitted outputs read block-wise, printed kernels) against the"
          " relaxed calculus HL.RStep (asserted):")
    print(f"  relaxed steps as printed: to lines {ok}")
    print(f"  printed slowdown time below c max(pin rest, b, time k), the least any slowdown rule allows: lines"
          f" {kinds['slow']} (largest gap {float(max(a for b in lit.values() for kd, a in b if kd == 'slow')):.3e});"
          f" line 6 -> 7: c * 1.155762944 = {float(lb7):.15f} > 1.5")
    print(f"  printed output of the innermost block lowered (convM, speedM need it >= the old): lines"
          f" {kinds['lowered']} (1.040108911 -> 1.040108909 at line 12, 1.040108911 -> 1.040108908 at line 22)")
    print(f"  other failures (convM a - s above the printed output, or speedM with no admissible x): lines"
          f" {kinds['other']}")
    print(f"  printed log n output 1 below max(b, e) (row D3): lines {kinds['log']}")
    print(f"  every failure other than the log n outputs is by at most {float(max(gaps)):.1e}; the numerical"
          " origin of these discrepancies is not determined, and the comparison uses the exact replay")
    d3 = d3_literal(printed, d)
    assert {k for k, v in d3.items() if v[4]} == {16, 19}, d3
    assert {k for k, v in d3.items() if v[3]} == {16}, d3
    assert "other" in [b[0] for b in lit[13]] and "lowered" in [b[0] for b in lit[22]]
    x19, mg19, pg19 = d3[19][:3]
    assert x19 == Q("0.439049244") and mg19 == Q("1.0401089109") and pg19 == Q("1.040108911"), d3[19]
    print("row D3, the printed Lemma 3.3 transitions to lines 13, 16, 19, 22 with any log n output >= 0 allowed"
          " (HY.SpeedLog; relaxed HL.Loose), omitted outputs read block-wise (asserted):")
    for k, (x, mg, pg, exact, loose) in d3.items():
        print(f"  line {k}: x = {float(x):.9f}, merged guess {float(mg):.10f}, printed {float(pg):.9f};"
              f" exact HY.SpeedLog step: {'yes' if exact else 'no'}; HL.Loose step: {'yes' if loose else 'no'}")
    print("  (line 13: no admissible x; line 22: the existential output is lowered; HL.Loose.speedM keeps both"
          " conditions)")
    c2 = Q("1.29784399")
    states2 = replay(printed, c2, d, "max")[1]
    end2 = states2[-1][1][1]
    assert states2[-1][0] == [] and end2 < start and f"{float(end2):.12f}" == "1.751958432856", end2
    print(f"at c = 1.29784399 the same replay passes every side condition and ends at {float(end2):.15f}, strictly below"
          f" its start {float(start):.9f} (asserted)")
    if "--tex" in sys.argv[1:]:
        print("rows of the table of A.2 in the paper (LaTeX):")
        for r in tex_rows:
            print(r)
    return 0


def sig(x, digits=2):
    if x == 0:
        return "0"
    m, e = f"{float(x):.{digits - 1}e}".split("e")
    return f"${m}\\cdot10^{{{int(e)}}}$"


def table_rows(per, raw_g, states, worst_k):
    """The body of the A.2 table: for each transition the rule, the largest kernel and guess deviations (two
    significant digits; four for the overall largest kernel deviation), and the notes D1 (overall largest kernel
    deviation), D2 (printed guess lowered) and D3 (carried log n output off the block-wise default by > 1e-7)."""
    d3 = {k for k, (blocks, ker) in enumerate(states) for q, g, o in blocks if abs(o - max(g, Q(1))) > Q(1, 10**7)}
    cells = []
    for k, r, par, kd, gd, lower in per:
        notes = []
        if lower:
            notes.append("D2")
        if k in d3:
            notes.append("D3")
        if kd == worst_k:
            notes.append("D1")
        g = sig(gd)
        if k == raw_g[0][0]:
            g += f" (first guess ${float(raw_g[0][1]):.9f}$)"
        if notes:
            g += "; " + ", ".join(notes)
        cells.append(f"{k} & {r} & {sig(kd, 4 if kd == worst_k else 2)} & {g}")
    half = len(cells) // 2
    return [f"{cells[i]} & {cells[i + half]}\\\\" for i in range(half)]


if __name__ == "__main__":
    sys.exit(main())
