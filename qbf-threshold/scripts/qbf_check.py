# SPDX-License-Identifier: Apache-2.0
"""Independent checker for QBF_k certificates, written from W13 TOCT Def. 4.1 + §5 (shares no code
with the generator).  Lines are W13 classes (Q1 n^{a1})^{b2} ... (Qm n^{am})^{b_{m+1}} DTS[n^{a_{m+1}}],
b1 = 1.  Rules:
  Speedup Rule 0 (m = 0): (Q n^x)^{max{x,1}} (Q' n^0)^1 DTS[n^{a-x}],          0 <= x <= a-1
  Speedup Rule 1 (m > 0): ...(Qm n^{max{am,x}})^{max{x,b_{m+1}}} (Q' n^0)^{b_{m+1}} DTS[n^{a-x}], 0 <= x <= a-1
  Slowdown (QBF_k: remove j innermost blocks, 1 <= j <= k):
     new kernel = c * max{kernel, a_i and b_i for the removed blocks i (in-front b of the outermost
     removed block included), b_{m+1}}.
Normal form (Def 4.2): first DTS[n^{a0}], last DTS[n^{a'}] with a' < a0 (strict), no other DTS line."""
import sys, json
from fractions import Fraction


def check(path):
    d = json.load(open(path))
    K = int(d['k']); c = Fraction(d['c']); a0 = Fraction(d['a0'])
    assert a0 >= 1
    quants = []   # outermost first
    guess = []    # a_i
    sup = [Fraction(1)]  # b_1 .. b_{m+1}; sup[i] is the superscript in front of block i+1 (sup[m] = kernel input)
    kern = a0
    nops = len(d['ops'])
    for t, (kind, val) in enumerate(d['ops']):
        m = len(quants)
        if kind == 'S':
            x = Fraction(val)
            assert 0 <= x <= kern - 1, ('x out of range', t)
            if m == 0:
                quants = ['E', 'A']; guess = [x, Fraction(0)]
                sup = [Fraction(1), max(x, Fraction(1)), Fraction(1)]
            else:
                bm1 = sup[m]
                guess[m - 1] = max(guess[m - 1], x)
                sup[m] = max(x, bm1)
                quants.append('A' if quants[-1] == 'E' else 'E')
                guess.append(Fraction(0))
                sup.append(bm1)
            kern = kern - x
        elif kind == 'P':
            j = int(val)
            assert 1 <= j <= K and j <= m, ('bad pop', t)
            lo = m - j
            cand = [kern] + guess[lo:m] + sup[lo:m + 1]
            kern = c * max(cand)
            quants = quants[:lo]; guess = guess[:lo]; sup = sup[:lo + 1]
        else:
            raise ValueError(kind)
        for i in range(len(quants) - 1):
            assert quants[i] != quants[i + 1]
        if t < nops - 1:
            assert len(quants) > 0, ('intermediate DTS line', t)
    assert len(quants) == 0
    return K, c, a0, kern, nops + 1


if __name__ == '__main__':
    for p in sys.argv[1:]:
        K, c, a0, fin, lines = check(p)
        print(p, 'k=%d c=%s lines=%d final/a0=%.6f' % (K, c, lines, fin / a0), 'VALID REFUTATION' if fin < a0 else 'NOT A REFUTATION')
