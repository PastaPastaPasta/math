#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact re-implementation of HLM.absCheck (PastaMath/OneTapeThreshold/AbsCheck.lean), run on the three
level lists and abstract-state lists that PastaMath/OneTapeThreshold/Ceiling.lean checks.

For each ceiling it prints c0, d, theta0 (and whether theta0 = c0^2 - c0/(d+1)), the levels (P, theta),
the number of abstract states, and whether the check accepts. It also runs two perturbed checks, which
should both reject: c0 lowered by 1/10^4 with theta0 recomputed as c0^2 - c0/(d+1) (levels and states
unchanged), and the last abstract state removed.

usage: abs_check.py ../../PastaMath/OneTapeThreshold/Ceiling.lean
Python 3 standard library only; exact arithmetic (fractions.Fraction)."""
import re
import sys
from fractions import Fraction as Q


def frac(s):
    s = s.strip()
    m = re.fullmatch(r"\((-?\d+) / (\d+) : ℚ\)", s) or re.fullmatch(r"\((-?\d+) : ℚ\)", s)
    return Q(int(m.group(1)), int(m.group(2)) if m.lastindex == 2 else 1)


def list_lines(src, name):
    i = src.find("def " + name + " :")
    if i < 0:
        return None
    j = src.find(":= [\n", i)
    if j < 0 or src.find("\n", i) < j:
        return None
    out = []
    for line in src[j + 5:].split("\n"):
        if line.strip() == "]":
            break
        if line.rstrip().endswith("]") and line.rstrip().endswith(")]"):
            out.append(line.rstrip()[:-1])
            break
        out.append(line)
    return out


def parse(path):
    src = open(path).read()
    out = []
    for m in re.finditer(r"theorem (absD\d)_ok : absCheck \((\d+) / (\d+) : ℚ\) \((\d+) : ℚ\) \((\d+) / (\d+) : ℚ\) (lvD\d) (absD\d)", src):
        name = m.group(1)
        c = Q(int(m.group(2)), int(m.group(3))); d = Q(int(m.group(4))); th0 = Q(int(m.group(5)), int(m.group(6)))
        lvs = re.search(r"def " + m.group(7) + r" : List \(ℚ × ℚ\) := \[(.*)\]\n", src).group(1)
        lv = [(Q(int(a), int(b)), Q(int(e), int(f))) for a, b, e, f in
              re.findall(r"\(\((\d+) / (\d+) : ℚ\), \((\d+) / (\d+) : ℚ\)\)", lvs)]
        raw = list_lines(src, name + "Raw")
        states = []
        if raw:
            for line in raw:
                mm = re.match(r"\s*\(\((-?\d+), (\d+)\), \((-?\d+), (\d+)\), \((-?\d+), (\d+)\), (\d+), \[(.*)\]\),?$", line)
                A, L, D = (Q(int(mm.group(1)), int(mm.group(2))), Q(int(mm.group(3)), int(mm.group(4))),
                           Q(int(mm.group(5)), int(mm.group(6))))
                iv = [(Q(int(a), int(b)), int(j)) for a, b, j in re.findall(r"\(\((-?\d+), (\d+)\), (\d+)\)", mm.group(8))]
                states.append(((A, L, D, int(mm.group(7))), iv))
        else:
            for line in list_lines(src, name):
                mm = re.match(r"\s*\(⟨(.*?), (.*?), (.*?), (\d+)⟩, \[(.*)\]\),?$", line)
                iv = [(frac(y), int(j)) for y, j in re.findall(r"\((\([^()]*\)), (\d+)\)", mm.group(5))]
                states.append(((frac(mm.group(1)), frac(mm.group(2)), frac(mm.group(3)), int(mm.group(4))), iv))
        out.append(dict(name=name, c=c, d=d, th0=th0, lv=lv, S=states))
    return out


def qf(d, s):
    A, L, D, m = s
    return max(A * L * d / (A + L * d), A * (1 + m * d) / (A * D + m * d))


def iv_ok(c, q, A, lt, iv):
    if not iv:
        return False
    for k, (y, j) in enumerate(iv):
        if j >= len(lt):
            return False
        P, th = lt[j]
        if not (P <= A or P <= q * y):
            return False
        if k == len(iv) - 1:
            if not th / c <= q:
                return False
        else:
            y2 = iv[k + 1][0]
            if not ((th / c * y2 <= A or th / c <= q) and y <= y2):
                return False
    return True


def st_ok(c, d, lt, s, iv):
    A, L, D, m = s
    return 0 < A and 0 <= L and 0 < D and bool(iv) and iv[0][0] == 0 and iv_ok(c, qf(d, s), A, lt, iv)


def prep(c, p, s):
    k = max(c, p[0]); A, L, D, m = s
    return (max(k, p[1] * A), p[1] * A, 1 / k + D / p[1], m + 1)


def done(c, d, th0, s):
    A, L, D, m = s
    return th0 / c <= A * L * d / (A + L * d)


def dom(s, t):
    return t[0] <= s[0] and t[1] <= s[1] and s[2] <= t[2] and t[3] <= s[3]


def closed(c, d, th0, lt, S, s):
    return all(done(c, d, th0, prep(c, p, s)) or any(dom(prep(c, p, s), t) for t, _ in S) for p in lt)


def abs_check(c, d, th0, lv, S):
    lt = [(Q(0), th0)] + lv
    return (1 <= c and 0 <= d and all(1 <= th <= c and 0 <= P for P, th in lt)
            and all(st_ok(c, d, lt, s, iv) for s, iv in S)
            and closed(c, d, th0, lt, S, (Q(1), Q(0), Q(1), 0))
            and all(closed(c, d, th0, lt, S, s) for s, _ in S))


def main(path):
    ok = True
    for x in parse(path):
        c, d, th0 = x["c"], x["d"], x["th0"]
        acc = abs_check(c, d, th0, x["lv"], x["S"])
        ok &= acc
        print(f"{x['name']}: c0 = {c} = {float(c)}, d = {d}, theta0 = {th0} "
              f"({'=' if th0 == c * c - c / (d + 1) else '!='} c0^2 - c0/(d+1)), {len(x['S'])} abstract states: "
              f"{'ACCEPT' if acc else 'REJECT'}")
        for P, th in x["lv"]:
            print(f"    level P = {float(P):.6f}, theta = {th} = {float(th)}")
        c2 = c - Q(1, 10 ** 4)
        low = abs_check(c2, d, c2 * c2 - c2 / (d + 1), x["lv"], x["S"])
        cut = abs_check(c, d, th0, x["lv"], x["S"][:-1])
        print(f"    perturbed: c0 - 1/10^4 = {c2}: {'ACCEPT' if low else 'REJECT'}; "
              f"last abstract state removed: {'ACCEPT' if cut else 'REJECT'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
