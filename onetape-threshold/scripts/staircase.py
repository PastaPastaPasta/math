#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""The staircase recursion of the paper (Section 7.2) and the numbers derived from it. None of this is
kernel-checked; it is numerical evidence for the conjectured threshold.

Recursion (top normalised to 1; d >= 1, c > 1):
  level 0:   Psi_0 = c, r_0 = c(1+d)/(c(1+d) - 1), g_0 = Psi_0/r_0, S_{-1} = 1, S_0 = S_{-1}/(c g_0) + 1/Psi_0;
  level h+1: n_h = 1 + (h+2) d, Psi_{h+1} = c g_h Psi_h,
             r_{h+1} = max( n_h/(n_h - S_h/c),  (c g_h + n_h + (r_h/c) S_{h-1})/n_h ),
             g_{h+1} = Psi_{h+1}/r_{h+1},  S_{h+1} = S_h/(c g_{h+1}) + 1/Psi_{h+1}.
Level h+1 exists iff n_h > S_h/c, r_{h+1} <= 1 + 1/d and r_{h+1} > c Psi_h (equivalently g_{h+1} < g_h).
Verdict at c: REF if some existing level has c g_h < 1; STOP if the staircase ends with c g_h > 1 for every
existing level. c*_stair(d) is the supremum of the c in [1 + 1/(4d), 1 + 1/d] with verdict REF. That the verdict is monotone in c
(REF below a single boundary, STOP above it) is observed numerically, not proved; without it, the bisection
locates a point where the verdict changes, not the supremum.

usage:
  staircase.py levels C D [H]     the levels at c = C (decimal), dimension D
  staircase.py threshold D DIGITS bisect for c*_stair(D) in interval arithmetic (directed rounding);
                                  every verdict used is certified by the intervals (the verdicts at the
                                  exact endpoints 1 + 1/(4d) and 1 + 1/d on outward-rounded enclosures,
                                  the later ones at decimal points, which are exact); the printed digits
                                  are those shared by the two ends of a bracket of width 10^-DIGITS
                                  with opposite certified verdicts (a numerical estimate of
                                  c*_stair: the bisection assumes the verdict is monotone in c)
  staircase.py appear D [K]       c_1, ..., c_K, where c_h is the point found by float bisection on
                                  [1 + 1/(4d), 1 + 1/d] at which the predicate "the recursion reaches
                                  level h or refutes before reaching it" (exists_level) changes from
                                  true to false; a numerical estimate. Asserts that at c_h - 2e-6
                                  the recursion reaches level h without refuting before it
  staircase.py roots              r_d (largest real root of Williams's p_d), sqrt(1+1/d), 1+1/(d+1), and the
                                  roots of the cubics at which level 1 first appears, for d = 1, 2, 3
Python 3 standard library only."""
import sys
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING, getcontext
from fractions import Fraction as Fr


def recursion(c, d, H, num):
    one = num(1)
    k = c * (1 + d)
    r = k / (k - one); P = c; g = P / r
    Sprev = one; S = Sprev / (c * g) + one / P
    out = [(r, P, g, "basin")]
    for h in range(H):
        cg = c * g
        if num.lt1(cg):
            return "REF", out
        if not num.gt1(cg):
            return "UNDEC", out
        n = num(1 + (h + 2) * d)
        den = n - S / c
        if not num.pos(den):
            return ("STOP" if num.nonpos(den) else "UNDEC"), out
        rbr = n / den
        rfr = (c * g + n + (r / c) * Sprev) / n
        rn = num.max(rbr, rfr)
        kind = num.which(rbr, rfr)
        Pn = c * g * P
        if num.gt(rn, one + one / num(d)) or num.le(rn, c * P):
            return "STOP", out
        if not (num.le(rn, one + one / num(d)) and num.gt(rn, c * P)):
            return "UNDEC", out
        Sprev = S
        r, P, g = rn, Pn, Pn / rn
        S = S / (c * g) + one / P
        out.append((r, P, g, kind))
    return "UNDEC", out


class Flt(float):
    pass


class FloatNum:
    def __call__(self, x): return float(x)
    def lt1(self, x): return x < 1
    def gt1(self, x): return x > 1
    def pos(self, x): return x > 0
    def nonpos(self, x): return x <= 0
    def max(self, a, b): return max(a, b)
    def which(self, a, b): return "branch" if a >= b else "fresh"
    def gt(self, a, b): return a > b
    def le(self, a, b): return a <= b


class Iv:
    __slots__ = ("lo", "hi")
    F = C = None

    def __init__(self, lo, hi=None):
        self.lo = lo; self.hi = lo if hi is None else hi

    @staticmethod
    def of(x):
        return x if isinstance(x, Iv) else Iv(D(x))

    def __add__(s, o):
        o = Iv.of(o); return Iv(Iv.F.add(s.lo, o.lo), Iv.C.add(s.hi, o.hi))
    __radd__ = __add__

    def __sub__(s, o):
        o = Iv.of(o); return Iv(Iv.F.subtract(s.lo, o.hi), Iv.C.subtract(s.hi, o.lo))

    def __rsub__(s, o):
        return Iv.of(o) - s

    def __mul__(s, o):
        o = Iv.of(o); assert s.lo > 0 and o.lo > 0
        return Iv(Iv.F.multiply(s.lo, o.lo), Iv.C.multiply(s.hi, o.hi))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = Iv.of(o); assert s.lo > 0 and o.lo > 0
        return Iv(Iv.F.divide(s.lo, o.hi), Iv.C.divide(s.hi, o.lo))

    def __rtruediv__(s, o):
        return Iv.of(o) / s


class IvNum:
    def __call__(self, x): return Iv(D(x))
    def lt1(self, x): return x.hi < 1
    def gt1(self, x): return x.lo > 1
    def pos(self, x): return x.lo > 0
    def nonpos(self, x): return x.hi <= 0
    def max(self, a, b): return Iv(max(a.lo, b.lo), max(a.hi, b.hi))
    def which(self, a, b): return "branch" if a.lo >= b.hi else ("fresh" if b.lo >= a.hi else "either")
    def gt(self, a, b): return a.lo > b.hi
    def le(self, a, b): return a.hi <= b.lo


def levels(cs, d, H=200):
    getcontext().prec = 60
    v, out = recursion(float(D(cs)), d, H, FloatNum())
    print(f"c = {cs}, d = {d}: verdict {v}")
    for h, (r, P, g, kind) in enumerate(out):
        print(f"  level {h:3d} ({kind:6s}): r = {r:.6f}  Psi = {P:.6f}  c*g = {float(D(cs)) * g:.6f}")


def threshold(d, digits):
    prec = digits + 40
    Iv.F = Context(prec=prec, rounding=ROUND_FLOOR); Iv.C = Context(prec=prec, rounding=ROUND_CEILING)
    num = IvNum()
    H = 40 * digits + 400
    # the exact endpoints 1 + 1/(4d) and 1 + 1/d, enclosed in outward-rounded intervals; a verdict
    # certified on an enclosure holds at every point of it, in particular at the exact endpoint and at
    # the decimal ends of the enclosure, from which the bisection starts
    ends = [Fr(4 * d + 1, 4 * d), Fr(d + 1, d)]
    encl = [Iv(Iv.F.divide(D(q.numerator), D(q.denominator)), Iv.C.divide(D(q.numerator), D(q.denominator)))
            for q in ends]
    vlo, vhi = recursion(encl[0], d, H, num)[0], recursion(encl[1], d, H, num)[0]
    assert (vlo, vhi) == ("REF", "STOP"), (vlo, vhi)
    print(f"d = {d}: verdict REF certified on an enclosure of c = {ends[0]}, STOP on an enclosure of c = {ends[1]}")
    lo, hi = encl[0].hi, encl[1].lo
    q = D(10) ** (-digits)
    while Iv.C.subtract(hi, lo) > q:
        mid = Iv.F.divide(Iv.F.add(lo, hi), 2)
        v = recursion(Iv(mid), d, H, num)[0]
        if v == "REF":
            lo = mid
        elif v == "STOP":
            hi = mid
        else:
            print("undecided at", mid); break
    vl, ol = recursion(Iv(lo), d, H, num)
    vh, oh = recursion(Iv(hi), d, H, num)
    kinds = sorted({k for *_, k in ol[1:]})
    a_, b_ = str(lo), str(hi)
    k = 0
    while k < min(len(a_), len(b_)) and a_[k] == b_[k]:
        k += 1
    print(f"d = {d}: c*_stair in [{a_[:digits + 4]}..., {b_[:digits + 4]}...]")
    print(f"  common digits of the two ends ({k - 2} decimals): {a_[:k]}")
    print("  (the verdicts at the two ends are certified; that these are digits of the supremum assumes that the"
          " verdict is monotone in c, which is not proved)")
    print(f"  verdict {vl} at the lower end after {len(ol) - 1} levels, {vh} at the upper end after {len(oh) - 1} levels;"
          f" kinds of r_(h+1) used at the lower end: {kinds}")


def exists_level(c, d, h):
    """True if the recursion at c reaches level h, or refutes (verdict REF) before reaching it. A refutation
    stops the recursion, so this is not "level h exists" in the sense of the paper when the recursion
    refutes early: at d = 1, c = 5/4 level 0 already refutes, and continuing past it would give a level-2
    candidate r_2 = 42375/13639 > 1 + 1/d."""
    v, out = recursion(c, d, 2000, FloatNum())
    return v == "REF" or len(out) - 1 >= h


def appear(d, K=6):
    res = []
    for h in range(1, K + 1):
        lo, hi = 1 + 1 / (4 * d), 1 + 1 / d
        for _ in range(200):
            m = (lo + hi) / 2
            if exists_level(m, d, h):
                lo = m
            else:
                hi = m
        res.append(lo)
    print(f"d = {d}: boundary c_h of 'reaches level h or refutes earlier' (float bisection): " + ", ".join(f"c_{h} = {x:.6f}" for h, x in enumerate(res, 1)))
    for h, x in enumerate(res, 1):
        v, out = recursion(x - 2e-6, d, 2000, FloatNum())
        assert len(out) - 1 >= h, (d, h, v, len(out) - 1)
    print(f"  at c_h - 2e-6, h = 1..{K}, the recursion reaches level h without refuting before it (asserted)")


def poly_root(coef, lo, hi, it=200):
    f = lambda x: sum(Fr(a) * x ** k for k, a in enumerate(coef))
    lo, hi = Fr(lo), Fr(hi)
    assert f(lo) * f(hi) < 0
    for _ in range(it):
        m = (lo + hi) / 2
        if (f(m) > 0) == (f(hi) > 0):
            hi = m
        else:
            lo = m
    return lo


def roots():
    cubic = {1: [2, -13, -2, 8], 2: [6, -46, -9, 36], 3: [12, -113, -20, 96]}
    for d in (1, 2, 3):
        p = [d * (d + 1), -((2 * d + 1) * (d + 1) ** 2 + 1), 2 * (d + 1), -d * d, -2 * (d + 1) * (2 * d + 1),
             (2 * d + 1) * (d + 1) ** 2]
        rd = poly_root(p, Fr(1001, 1000), 2)
        cr = poly_root(cubic[d], Fr(11, 10), 2)
        getcontext().prec = 40
        c1 = None
        lo, hi = 1 + 1 / (4 * d), 1 + 1 / d
        for _ in range(200):
            m = (lo + hi) / 2
            if exists_level(m, d, 1):
                lo = m
            else:
                hi = m
        print(f"d = {d}: r_d = {float(rd):.10f}  sqrt(1+1/d) = {(1 + 1 / d) ** 0.5:.6f}  1+1/(d+1) = {1 + 1 / (d + 1):.6f}"
              f"  cubic root = {float(cr):.12f}  boundary c_1 (reaches level 1 or refutes earlier) = {lo:.12f}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "levels":
        levels(a[1], int(a[2]), int(a[3]) if len(a) > 3 else 200)
    elif a[0] == "threshold":
        threshold(int(a[1]), int(a[2]))
    elif a[0] == "appear":
        appear(int(a[1]), int(a[2]) if len(a) > 2 else 6)
    elif a[0] == "roots":
        roots()
