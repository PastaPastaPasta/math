#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Untrusted generator of staircase DAG certificates for HD.dagCheck / HDS.dagCheck (paper Section 4.4).

usage: stair_cert.py CNUM CDEN D M SH MAXLEVELS OUT.json [TOL]
  c = CNUM/CDEN, dimension D, grid M, values in units of 2^-SH, at most MAXLEVELS levels, climb tolerance 1/TOL
  (default TOL = 10^8).

Structure: level 0 is a climb of basin nodes up to alpha_1; level h+1 is a fresh node with chain
[K_h, K_h, K_(h-1), ..., K_0] followed by a climb [previous node, K_h, ..., K_0]; the kink K_(h+1) is the top of
the climb. It stops at the first kink with c*phi < 1 (the root). The output is only a candidate: it is a proof
only if HD.dagCheck / HDS.dagCheck accept it (check with dag_check.py --json OUT.json). Python 3 standard
library only."""
import sys, json
from fractions import Fraction as Fr
cn, cd, d, M, SH, maxlev = map(int, sys.argv[1:7]); out = sys.argv[7]
c = Fr(cn, cd); S = 1 << SH
def fl(x): return x.numerator // x.denominator
def cl(x): return -((-x.numerator) // x.denominator)
def fdy(x): return Fr(fl(x * S), S)
nodes = []
def phiF(q): return Fr(nodes[q]['phi'], S)
def plan(t, seq, W0):
    i = d * (t - M); j = t; w = W0; steps = []
    if i > M or t <= M: return None
    m = len(seq)
    tl = nodes[seq[-1]]['t']
    L = max(M, i) - i + cl(Fr(tl) / c)
    for l, q in enumerate(seq):
        tq = nodes[q]['t']; ph = phiF(q)
        if l < m - 1:
            win = fdy(w / (c * ph))
            later = m - 2 - l
            ku = min(fl(c * win * M * M / tq), j, j + i - L - later * (max(M, i) - i))
            if ku < M or ku < i: return None
            jn = j + i - ku
            if jn < 1: return None
            steps.append((ku, q + 1, w)); j = jn; w = win
        else:
            ku = min(fl((j + i) * c * M / (c * M + tq)), j, j + i - M)
            if ku < M or ku < i: return None
            jp = j + i - ku; u = Fr(ku, M); Wp = max(Fr(1), Fr(jp, M))
            alpha = c * max(Fr(1), Wp / u)
            if alpha < Fr(tq, M): return None
            val = u * ph * alpha
            if val > w or val < 1: return None
            steps.append((ku, q + 1, w)); return steps, jp
    return None
def best(t, seq, lo, hi):
    if plan(t, seq, Fr(hi, S)) is None: return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if plan(t, seq, Fr(mid, S)) is None: lo = mid
        else: hi = mid
    return hi
def add(t, seq, W0i):
    steps, p = plan(t, seq, Fr(W0i, S))
    W0 = Fr(W0i, S); kap = Fr(t, M); ph = cl(W0 / kap * S)
    assert Fr(ph, S) * kap >= 1
    nodes.append(dict(t=t, p=p, phi=ph, steps=[(ku, r, cl(w * S)) for ku, r, w in steps], seq=seq))
    return len(nodes) - 1
def first_feasible(seq, tlo, thi, Wcap):
    if best(thi, seq, 0, Wcap) is None: return None
    lo, hi = tlo - 1, thi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if best(mid, seq, 0, Wcap) is None: lo = mid
        else: hi = mid
    return hi
def maxt(seq, tlo, thi, Vcap):
    ta = first_feasible(seq, tlo, thi, cl(3 * S))
    if ta is None or best(ta, seq, 0, Vcap) is None: return None
    lo, hi = ta, thi + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if best(mid, seq, 0, Vcap) is None: hi = mid
        else: lo = mid
    return lo
def climb(first, seqf, tol):
    prev = first
    tmax = M + M // d
    while True:
        tp = nodes[prev]['t']; seq = seqf(prev)
        V = Fr(nodes[prev]['phi'], S) * Fr(tp, M)
        cap = cl(V * (1 + tol) * S)
        tn = maxt(seq, tp + 1, tmax, cap)
        if tn is None or tn - tp < 2: return prev
        prev = add(tn, seq, best(tn, seq, 0, cap))
t0 = M + cl(Fr(M, 1 + d))
i0 = d * (t0 - M); jp0 = t0 + i0 - M; assert jp0 >= M and i0 <= M
w0 = cl(c * max(Fr(1), Fr(jp0, M)) * S)
nodes.append(dict(t=t0, p=jp0, phi=cl(Fr(w0, S) / Fr(t0, M) * S), steps=[(M, 0, w0)], seq=['pop']))
tol = Fr(1, int(sys.argv[8])) if len(sys.argv) > 8 else Fr(1, 10**8)
K = [climb(0, lambda prev: [prev], tol)]
def ratio(q): return float(c * phiF(q))
print("level 0 kink t/M=%.9f psi=%.9f c*g=%.9f nodes=%d" % (nodes[K[0]]['t']/M, float(phiF(K[0])*Fr(nodes[K[0]]['t'],M)), ratio(K[0]), len(nodes)))
root = K[0] if c * phiF(K[0]) < 1 else None
for h in range(maxlev if root is None else 0):
    seqf = [K[h], K[h]] + K[::-1][1:]
    tmax = M + M // d
    hiW = cl(3 * S)
    ta = first_feasible(seqf, nodes[K[h]]['t'], tmax, hiW)
    if ta is None: print("no fresh node at level", h + 1); break
    b0 = best(ta, seqf, 0, hiW)
    lim = cl(Fr(b0, S) * (1 + tol) * S)
    lo = maxt(seqf, ta, tmax, lim)
    f = add(lo, seqf, best(lo, seqf, 0, lim))
    kink = climb(f, lambda prev, h=h: [prev] + K[::-1], tol)
    K.append(kink)
    print("level %d fresh t/M=%.9f  kink t/M=%.9f psi=%.9f c*g=%.9f nodes=%d" % (h + 1, nodes[f]['t']/M, nodes[kink]['t']/M,
          float(phiF(kink)*Fr(nodes[kink]['t'],M)), ratio(kink), len(nodes)), flush=True)
    if c * phiF(kink) < 1: root = kink; break
if root is None:
    q = min(range(len(nodes)), key=lambda q: phiF(q)); print("no refutation; best c*phi", ratio(q)); root = q
json.dump(dict(c=[cn, cd], d=d, M=M, SH=SH, root=root, refutes=bool(c*phiF(root) < 1),
               nodes=[dict(t=n['t'], p=n['p'], phi=n['phi'], steps=n['steps']) for n in nodes]), open(out, 'w'))
print("root", root, "c*phi", ratio(root), "nodes", len(nodes), "steps", sum(len(n['steps']) for n in nodes))
