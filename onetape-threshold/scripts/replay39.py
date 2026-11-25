#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Replays the 38 rule tags of HY.cert39 (PastaMath/OneTapeThreshold/Proof39.lean) with a transcription of
Williams's rules written from the TOCT text (Lemma 7.1, Lemma 3.3 inside a prefix with Speedup Rule 1,
Lemma 7.2, and the combining of adjacent same-type blocks of §2), independent of the Lean definitions.

It checks every side condition, alternation, the strict normal form (DTIME_d first and last, no other
quantifier-free line, 1 <= a' < a), and the strict reading (kernel time >= input superscript, and
space <= time on DTISP lines), and prints the proof with exponents divided by 1000 (a0 = 10^5 is shown as
100.000); "log" is a log n block. Exact arithmetic; Python 3 standard library only.

With --log-one, --log-in or --log-sp it replays the same tags in the variant of the calculus in which the
new log n block of Lemma 3.3 has output superscript exactly 1, max(b, 1) or max(1, e) (instead of
max(b, e)), runs the same checks, and lists the lines that differ from the replay with max(b, e). This is a
script check only; Lean checks the 39-line proof for max(b, e) (HY.cert39_spec), and the variants only for
the staircase certificates. In every mode it also lists the Lemma 7.2 steps at which the output
superscript of the remaining prefix (b_k) is the strict maximum, i.e. where a slowdown maximum without b_k
(as displayed on p. A:36 of Williams's paper) would give a smaller exponent.

usage: replay39.py [--log-one | --log-in | --log-sp] ../../PastaMath/OneTapeThreshold/Proof39.lean"""
import re
import sys
from fractions import Fraction as Q


def tags(path):
    s = open(path).read()
    body = re.search(r"def cert39 : List Tag :=\n(.*?)\]\n", s, re.S).group(1)
    out = []
    for m in re.finditer(r"\.(convNew true|convMerge|speedMerge|slow)(?: \((\d+) / (\d+) : ℚ\))?", body):
        out.append((m.group(1).split()[0], Q(int(m.group(2)), int(m.group(3))) if m.group(2) else None))
    cn, cd, d, a0 = map(int, re.search(r"theorem cert39_ok : nfCheck \((\d+) / (\d+) : ℚ\) (\d+) (\d+) cert39", s).groups())
    return Q(cn, cd), d, Q(a0), out


def inp(blocks):
    return blocks[-1][2] if blocks else Q(1)


ELL = {
    "max": ("max(b, e)", lambda o, e: max(o, e)),
    "one": ("exactly 1", lambda o, e: Q(1)),
    "in": ("max(b, 1)", lambda o, e: max(o, Q(1))),
    "sp": ("max(1, e)", lambda o, e: max(Q(1), e)),
}


def step(c, d, line, tag, p, ell="max"):
    blocks, ker = line
    b = inp(blocks)
    if tag in ("convNew", "convMerge"):
        assert ker[0] == "T" and 0 < p <= ker[1] and b >= 1
        a = ker[1]
        if tag == "convNew":
            assert not blocks, "the 39-line proof opens a block only on the first line"
            nb = [("E", a - p, max(a - p, b))]
        else:
            q, g, o = blocks[-1]
            nb = blocks[:-1] + [(q, max(g, a - p), max(a - p, o))]
        return nb, ("S", a, d * p), "L7.1"
    if tag == "speedMerge":
        assert ker[0] == "S"
        a, e = ker[1], ker[2]; x = p
        assert a >= 1 and 0 <= e <= a - x and 0 <= x <= a - 1 and b >= 1
        q, g, o = blocks[-1]
        other = "A" if q == "E" else "E"
        nb = blocks[:-1] + [(q, max(g, x + e), max(o, x + e)), (other, Q(0), ELL[ell][1](o, e))]
        return nb, ("S", a - x, e), "L3.3"
    if tag == "slow":
        q, g, o = blocks[-1]
        bk = inp(blocks[:-1])
        assert bk >= 1 and o >= 1 and ker[1] >= 1 and g >= 0
        return blocks[:-1], ("T", c * max(bk, o, g, ker[1])), "L7.2"
    raise ValueError(tag)


def fmt(x):
    return f"{float(x) / 1000:.3f}"


def show(line):
    blocks, ker = line
    s = " ".join(f"({q} {'log' if g == 0 else 'n^' + fmt(g)})^{fmt(o)}" for q, g, o in blocks)
    k = f"DTIME_1[n^{fmt(ker[1])}]" if ker[0] == "T" else f"DTISP[n^{fmt(ker[1])}, n^{fmt(ker[2])}]"
    return (s + " " + k).strip()


def replay(c, d, a0, ts, ell):
    lines = [([], ("T", a0))]
    rules = [""]
    for tag, p in ts:
        nb, nk, r = step(c, d, lines[-1], tag, p, ell)
        lines.append((nb, nk)); rules.append(r)
    return lines, rules


def omitted_bk(lines, rules):
    out = []
    for i in range(1, len(lines)):
        if rules[i] == "L7.2":
            blocks, ker = lines[i - 1]
            q, g, o = blocks[-1]
            bk = inp(blocks[:-1])
            if bk > max(o, g, ker[1]):
                out.append(i)
    return out


def main(path, ell="max"):
    c, d, a0, ts = tags(path)
    lines, rules = replay(c, d, a0, ts, ell)
    n = len(lines) - 1
    for i, (blocks, ker) in enumerate(lines):
        assert all(blocks[k][0] != blocks[k + 1][0] for k in range(len(blocks) - 1)), "alternation"
        assert (0 < i < n) == bool(blocks), "normal form: quantifier-free lines only at the ends"
        assert inp(blocks) <= ker[1], "strict reading: time >= input"
        assert ker[0] == "T" or ker[2] <= ker[1], "space <= time"
    assert lines[-1][1][0] == "T" and 1 <= lines[-1][1][1] < a0
    gap, at = min((k[1] - inp(bl), i) for i, (bl, k) in enumerate(lines))
    print(f"c = {c} = {float(c)}, d = {d}, a0 = {a0}, {n + 1} lines"
          + ("" if ell == "max" else f", new log n block of Lemma 3.3 with output {ELL[ell][0]}"))
    for i, L in enumerate(lines):
        print(f"{i:2d} {rules[i]:5s} {show(L)}")
    print(f"final exponent {float(lines[-1][1][1])} < {a0}; a0 - a' = {float(a0 - lines[-1][1][1]):.6f}")
    near = [i for i, (bl, k) in enumerate(lines) if k[1] - inp(bl) < Q(1, 10**6)]
    print(f"all side conditions, alternation, normal form, time >= input and space <= time hold; "
          f"min(time - input) = {float(gap):.3g} (line {at}); time - input < 1e-6 on lines {near}")
    om = omitted_bk(lines, rules)
    print("Lemma 7.2 steps at which the output superscript of the remaining prefix (b_k) is the strict maximum, "
          "so that a maximum without b_k would give a smaller exponent: " + (str(om) if om else "none"))
    if ell != "max":
        ref, _ = replay(c, d, a0, ts, "max")
        diff = [i for i in range(n + 1) if lines[i] != ref[i]]
        kdiff = [i for i in range(n + 1) if lines[i][1] != ref[i][1]]
        print(f"lines that differ from the replay with output max(b, e): {diff}")
        print(f"lines whose kernel differs: {kdiff if kdiff else 'none'}; final exponent "
              + ("the same" if lines[-1] == ref[-1] else "different"))
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    ell = "max"
    for flag, name in (("--log-one", "one"), ("--log-in", "in"), ("--log-sp", "sp")):
        if flag in args:
            ell = name
            args.remove(flag)
    sys.exit(main(args[0], ell))
