#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact checker for the alternation-trading calculus of Mudigonda and Williams for
E.BPTIME[n] versus BPTS (arXiv 2012.00330, Definition 2.14 rules 2-5 and Lemma 5.1; numbering of
the arXiv version). Python standard library only; rule replays and parameter checks are exact (fractions.Fraction);
only the printed root of x^3 - x^2 - 1 is a floating-point bisection, for display.

A line is a list of blocks (Q n^a)^b, outermost first, followed by a kernel TS[n^d] or BPTS[n^d].
An x log n block is written with guess exponent 0. The input length in front of the first block
is n^1. The rules, transcribed from the paper:

  rule 3 (Theorem 2.10), on a quantifier-free BPTS line, 0 < x < d:
      BPTS[n^d] -> (E n^0)^1 (A n^x)^max(x,1) (E x log n)^1 TS[n^(d-x)]
  rule 4 (Corollary 2.11), innermost block (Q n^a)^b, BPTS kernel, 0 < x < d; the leading n^0
      block of Theorem 2.10 is absorbed into (Q n^a)^b (the paper's footnote), so the new block
      has the opposite quantifier:
      ... (Q n^a)^b BPTS[n^d] -> ... (Q n^a)^b (~Q n^x)^max(b,x) (Q x log n)^b TS[n^(d-x)]
  rule 2 (Corollary 2.8), innermost block (Q n^a)^b, TS kernel, 0 < x < d:
      ... (Q n^a)^b TS[n^d] -> ... (Q n^max(a,x))^max(b,x) (~Q x log n)^b TS[n^(d-x)]
  slowdown (Lemma 5.1, applied to a TS kernel through TS in BPTS), at least one block:
      ... (Q' n^a')^b' (Q n^a)^b K[n^d] -> ... (Q' n^a')^b' BPTS[n^(c*max(d, b, a, b'))]
      with b' = 1 if (Q n^a)^b is the outermost block.

A refutation (Lemma 5.2) is a sequence from BPTS[n^d] back to a quantifier-free BPTS[n^d'] with
d' < d. Besides the rule side conditions the checker asserts that every line is orderly (a <= b,
Lemma 2.17) and alternates.

Commands:
  python3 mw_check.py mw15                  replay the 15-step refutation at c = 1.467
  python3 mw_check.py macro                 one macro M(2) at c = 3/2: contraction factor 27/28
  python3 mw_check.py construct 3/2         generate and check the general construction at c
  python3 mw_check.py construct 8/5
  python3 mw_check.py cert PATH             regenerate the c = 8/5 certificate (M(8), a0 = 10000,
                                            T rounded up to 6 decimals, macro repeated while
                                            e >= sigma_8, i.e. unrounded T >= 1) and compare it
                                            with the tag list in the Lean file PATH
  python3 mw_check.py thm53                 the printed parameters of Theorem 5.3, and corrected ones
  python3 mw_check.py all [PATH]            everything above (cert only if PATH is given)
"""
import re
import sys
from fractions import Fraction as F

ONE = F(1)
EX, ALL = "E", "A"


def neg(q):
    return ALL if q == EX else EX


class RuleError(Exception):
    pass


def check_line(blocks, kernel, d):
    for i, (q, a, b) in enumerate(blocks):
        if not (0 <= a <= b):
            raise RuleError(f"block {i + 1} not orderly: a = {a}, b = {b}")
        if i > 0 and blocks[i - 1][0] == q:
            raise RuleError(f"blocks {i} and {i + 1} have the same quantifier")
    if kernel not in ("TS", "BPTS"):
        raise RuleError("bad kernel")


def step(c, line, tag):
    """Apply one rule. tag = ('r', x) randomized speedup (rule 3 or 4), ('d', x) rule 2,
    ('s',) slowdown. Returns (new line, rule name)."""
    blocks, kernel, d = line
    kind = tag[0]
    if kind in ("r", "d"):
        x = tag[1]
        if not (0 < x < d):
            raise RuleError(f"speedup parameter {x} not in (0, {d})")
    if kind == "r":
        if kernel != "BPTS":
            raise RuleError("randomized speedup needs a BPTS kernel")
        if not blocks:
            new = [(EX, F(0), ONE), (ALL, x, max(x, ONE)), (EX, F(0), ONE)]
            name = "Thm 2.10"
        else:
            q, a, b = blocks[-1]
            new = blocks + [(neg(q), x, max(b, x)), (q, F(0), b)]
            name = "Cor 2.11"
        out = (new, "TS", d - x)
    elif kind == "d":
        if kernel != "TS" or not blocks:
            raise RuleError("rule 2 needs a TS kernel and at least one block")
        q, a, b = blocks[-1]
        new = blocks[:-1] + [(q, max(a, x), max(b, x)), (neg(q), F(0), b)]
        out, name = (new, "TS", d - x), "Cor 2.8"
    elif kind == "s":
        if not blocks:
            raise RuleError("slowdown needs a block")
        q, a, b = blocks[-1]
        bprev = blocks[-2][2] if len(blocks) >= 2 else ONE
        out, name = (blocks[:-1], "BPTS", c * max(d, b, a, bprev)), "Lemma 5.1"
    else:
        raise RuleError("unknown tag")
    check_line(*out)
    return out, name


def run(c, a0, tags, show=False):
    line = ([], "BPTS", a0)
    if show:
        print(f" 0  {fmt(line)}")
    for i, t in enumerate(tags, 1):
        line, name = step(c, line, t)
        if show:
            par = f", x = {t[1]}" if t[0] != "s" else ""
            print(f"{i:2d}  ⊆ {fmt(line)}    [{name}{par}]")
    blocks, kernel, d = line
    ok = not blocks and kernel == "BPTS" and d < a0 and len(tags) >= 2
    return ok, d


def dec(v, digits=1):
    if v.denominator == 1:
        return str(v.numerator)
    return f"{float(v):.{digits}f}"


def fmt(line, digits=1):
    blocks, kernel, d = line
    parts = []
    for q, a, b in blocks:
        sym = "∃" if q == EX else "∀"
        parts.append(f"({sym}n^{dec(a, digits)})^{dec(b, digits)}")
    parts.append(f"{kernel}[n^{dec(d, digits)}]")
    return " ".join(parts)


# ---------------------------------------------------------------- the 15-step proof

MW15 = [("r", F(3830)), ("d", F(206250, 79)), ("d", F(105000, 59)), ("s",), ("s",), ("s",), ("s",),
        ("r", F(1550000, 491)), ("d", F(170000, 79)), ("d", F(1040000, 709)),
        ("s",), ("s",), ("s",), ("s",), ("s",)]


def cmd_mw15():
    c, a0 = F(1467, 1000), F(10000)
    print("15-step refutation at c = 1467/1000, a0 = 10000 (exponents rounded to 0.1):")
    ok, d = run(c, a0, MW15, show=True)
    print(f"final exponent {d} = {float(d):.6f} < {a0}: {ok}")
    r = mw21_root()
    print(f"largest root of x^3 - x^2 - 1: {r:.6f} < 1.467: {r < 1.467}")
    assert ok
    return ok


def mw21_root():
    lo, hi = 1.0, 2.0
    for _ in range(100):
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 - 1 < 0:
            lo = mid
        else:
            hi = mid
    return lo


# ---------------------------------------------------------------- the construction

def sigma(c, k):
    """sigma_0 = 1, sigma_{i+1} = sigma_i + c^i."""
    s = ONE
    for i in range(k):
        s += c ** i
    return s


def macro_tags(c, j, e, round_up=None):
    """M(j+1) from kernel e: one randomized speedup, j deterministic speedups, j+2 slowdowns,
    with T = e / sigma_{j+1} and parameters c^j T, c^(j-1) T, ..., T. With round_up = N, T is
    rounded up to a multiple of 1/N (this keeps the numbers in a long certificate short)."""
    t = e / sigma(c, j + 1)
    if round_up:
        t = F(-((-t.numerator * round_up) // t.denominator), round_up)
    tags = [("r", c ** j * t)] + [("d", c ** i * t) for i in range(j - 1, -1, -1)]
    return tags + [("s",)] * (j + 2)


def construct(c, j=None, a0=None, exhaust=False, round_up=None, max_macros=100000):
    """Iterate M(j+1) under the (E n^0)^1 block, then pop the block. By default the block is
    popped as soon as c*max(e,1) < a0; with exhaust=True the macro is repeated while
    e >= sigma_{j+1} (that is, T >= 1), as in the Lean proof of refutes_of_lt_phi.
    Default j: least j with c^(j+2) < sigma_{j+1}; default a0 = c*sigma_{j+1} + 1."""
    if j is None:
        j = 0
        while not c ** (j + 2) < sigma(c, j + 1):
            j += 1
            if j > 200:
                raise RuleError("no contracting macro (c >= golden ratio?)")
    s = sigma(c, j + 1)
    if a0 is None:
        a0 = c * s + 1
    tags, line, macros = [], ([], "BPTS", a0), 0
    while True:
        e = line[2]
        done = e < s if exhaust else c * max(e, ONE) < a0
        if line[0] and done:
            tags.append(("s",))
            line, _ = step(c, line, ("s",))
            break
        if macros >= max_macros:
            raise RuleError("too many macros")
        for t in macro_tags(c, j, e, round_up):
            tags.append(t)
            line, _ = step(c, line, t)
        macros += 1
    ok, d = run(c, a0, tags)
    return dict(j=j, rho=c ** (j + 2) / s, a0=a0, macros=macros, tags=tags, final=d, ok=ok)


def cmd_macro():
    c, e = F(3, 2), F(28)
    top = ([(EX, F(0), ONE)], "BPTS", e)
    print("One macro M(2) at c = 3/2 from (∃n^0)^1 BPTS[n^e], e = 28 (so T = e/σ_2 = 8):")
    line = top
    print(f"    {fmt(line)}")
    for t in macro_tags(c, 1, e):
        line, name = step(c, line, t)
        par = f", x = {t[1]}" if t[0] != "s" else ""
        print(f"  ⊆ {fmt(line)}    [{name}{par}]")
    factor = line[2] / e
    print(f"kernel factor {line[2]}/{e} = {factor}")
    assert factor == F(27, 28)
    for e2 in (F(7, 2), F(10), F(355, 3), F(10 ** 6)):
        line = ([(EX, F(0), ONE)], "BPTS", e2)
        for t in macro_tags(c, 1, e2):
            line, _ = step(c, line, t)
        assert line[2] / e2 == F(27, 28), e2
    print("same factor 27/28 at e = 7/2, 10, 355/3, 10^6 (any e >= 7/2, where T >= 1)")
    return True


def cmd_construct(cs):
    c = F(cs)
    r = construct(c)
    n = len(r["tags"])
    print(f"c = {c}: macro M({r['j'] + 1}), rho = {r['rho']} ≈ {float(r['rho']):.5f}, "
          f"{r['macros']} macros, {n} steps, a0 = {float(r['a0']):.4f} -> final "
          f"{float(r['final']):.4f}, refutation: {r['ok']}")
    assert r["ok"]
    return True


# ---------------------------------------------------------------- the Lean certificate

TAG_RE = re.compile(r"\.(r|d) \((\d+) / (\d+) : ℚ\)|\.s\b")


def parse_lean(path):
    text = open(path, encoding="utf-8").read()
    body = text[text.index("def mwcert"):text.index("theorem mwcert_ok")]
    tags = []
    for m in TAG_RE.finditer(body):
        if m.group(1):
            tags.append((m.group(1), F(int(m.group(2)), int(m.group(3)))))
        else:
            tags.append(("s",))
    return tags


def cmd_cert(path):
    c, a0 = F(8, 5), F(10000)
    lean = parse_lean(path)
    r = construct(c, j=7, a0=a0, exhaust=True, round_up=10 ** 6)
    same = lean == r["tags"]
    ok, d = run(c, a0, lean)
    print(f"Lean certificate: {len(lean)} steps; regenerated with M(8), a0 = 10000, T rounded up to")
    print(f"6 decimals, macro repeated while e >= sigma_8: {len(r['tags'])} steps, {r['macros']} "
          f"macros; identical: {same}")
    print(f"replay of the Lean list: final exponent {float(d):.4f} < 10000: {ok}")
    assert same and ok
    return True


# ---------------------------------------------------------------- Theorem 5.3

def cmd_thm53():
    print("Proof of Theorem 5.3 as printed: x1 = d/c^3, x_i = (c(1-eps))^(1-i) x1, eps = 1/k, d = 1.")
    print("Its chain needs d - sum(x_i) > 0 (rule 2 / Cor 2.8 side condition) and, for the steps")
    print("BPTS[n^(c^2 x_i)] ⊆ BPTS[n^(c x_(i-1))], c x_i <= x_(i-1).")
    for cs in ("1.40", "1.44", "1.46"):
        c = F(cs)
        for k in (2, 5, 10, 20, 50, 100):
            eps = F(1, k)
            x = [ONE / c ** 3]
            for i in range(2, k + 1):
                x.append(x[0] / (c * (1 - eps)) ** (i - 1))
            kern = 1 - sum(x)
            mono = all(c * x[i] <= x[i - 1] for i in range(1, k))
            print(f"  c = {cs}, k = {k:3d}: d - sum x_i = {float(kern):+.4f}, "
                  f"c x_i <= x_(i-1) for all i: {mono}")
    print("Corrected parameters x_i = c^(k-i) T, d = sigma_k T (the chain 1^k 0^(k+2) from")
    print("BPTS[n^d], including the final slowdown), checked exactly with the rules above:")
    for cs in ("1.46", "1.465", "1.466", "1.47"):
        c = F(cs)
        best = None
        for k in range(1, 61):
            t = F(10)
            d = sigma(c, k) * t
            tags = macro_tags(c, k - 1, d) + [("s",)]
            ok, dfin = run(c, d, tags)
            ratio = dfin / d
            if best is None or ratio < best[0]:
                best = (ratio, k)
        print(f"  c = {cs}: best final/initial over k <= 60 is {float(best[0]):.5f} (k = {best[1]})")
    print(f"  (largest root of x^3 - x^2 - 1 = {mw21_root():.5f})")
    return True


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    cmd = argv[0]
    if cmd == "mw15":
        cmd_mw15()
    elif cmd == "macro":
        cmd_macro()
    elif cmd == "construct":
        for cs in argv[1:] or ["3/2", "8/5"]:
            cmd_construct(cs)
    elif cmd == "cert":
        cmd_cert(argv[1])
    elif cmd == "thm53":
        cmd_thm53()
    elif cmd == "all":
        cmd_mw15()
        print()
        cmd_macro()
        print()
        cmd_construct("3/2")
        cmd_construct("8/5")
        print()
        if len(argv) > 1:
            cmd_cert(argv[1])
            print()
        cmd_thm53()
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
