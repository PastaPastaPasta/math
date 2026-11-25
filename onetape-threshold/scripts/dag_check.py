#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact re-implementation of the DAG checkers HD.dagCheck (literal reading) and HDS.dagCheck (strict
reading) of PastaMath/OneTapeThreshold/Dag.lean and DagStrict.lean, run on the node lists that the Lean
files PastaMath/OneTapeThreshold/StairD{1,2,3}.lean check.

For each certificate it prints c, d, the grid M, the number of nodes and speedup steps, the root ratio
c*phi_root (< 1 is required), whether both readings accept, the starting exponent a0 of the normal-form
proof that HD.nf_of_SC builds (a0 = kappa_root * max(M, 1) = t_root), and the number of lines of the derivation
that the soundness proof builds (HD.nf_of_SC with SC_speed / TC_of_SC), counted as if no level were closed
early (early closing only shortens it, so this is an upper bound).

usage: dag_check.py [--json FILE] LEAN_FILE...
  --json FILE  also check a generator output (stair_cert.py) and report whether it equals the Lean data.
Python 3 standard library only; all arithmetic is exact (fractions.Fraction)."""
import json
import re
import sys
from fractions import Fraction as Q

sys.setrecursionlimit(100000)


def parse_lean(path):
    s = open(path).read()
    raw = re.search(r"def (stairD\d)Raw : [^\n]*:= \[\n(.*?)\n\]\n", s, re.S)
    name, body = raw.group(1), raw.group(2)
    nodes = []
    for line in body.split("\n"):
        m = re.match(r"\s*\((\d+), (\d+), (\d+), \[(.*)\]\),?$", line)
        steps = [tuple(map(int, x)) for x in re.findall(r"\((\d+), (\d+), (\d+)\)", m.group(4))]
        nodes.append(dict(t=int(m.group(1)), p=int(m.group(2)), phi=int(m.group(3)), steps=steps))
    params = {}
    for kind in ("HD", "HDS"):
        m = re.search(kind + r"\.dagCheck \((\d+) / (\d+)\) (\d+) (\d+) (\d+) " + name + kind + r" (\d+) = true", s)
        params[kind] = tuple(map(int, m.groups()))
    assert params["HD"] == params["HDS"], "literal and strict checks use different parameters"
    cn, cd, d, M, SH, root = params["HD"]
    return dict(name=name, c=[cn, cd], d=d, M=M, SH=SH, root=root, nodes=nodes)


def check(cert, strict):
    c = Q(*cert["c"]); d = cert["d"]; M = cert["M"]; S = Q(2) ** cert["SH"]
    if not (1 <= c and 1 <= d and 1 <= M):
        return None, "parameters"
    tab = []

    def tval(r, alpha):
        if r == 0:
            return max(Q(1), alpha)
        if r - 1 >= len(tab):
            return None
        tr, ph = tab[r - 1]
        return ph * alpha if Q(tr, M) <= alpha else None

    def chain(i, p, j, steps):
        for k, (ku, r, w) in enumerate(steps):
            if not (M <= ku and i <= ku and ku <= j and (M if strict else 1) <= j + i - ku):
                return None
            j = j + i - ku
        if j != p:
            return None
        W = max(Q(1), Q(j, M))
        for ku, r, w in reversed(steps):
            v = tval(r, c * max(Q(1), W / Q(ku, M)))
            if v is None or not (1 <= Q(ku, M) * v <= Q(w) / S):
                return None
            W = Q(w) / S
        return W

    for k, nd in enumerate(cert["nodes"]):
        t = nd["t"]
        if not (M < t and d * (t - M) <= M):
            return None, f"node {k}: range"
        W = chain(d * (t - M), nd["p"], t, nd["steps"])
        if W is None:
            return None, f"node {k}: chain"
        ph = Q(nd["phi"]) / S
        if not (W / Q(t, M) <= ph and 1 <= ph * Q(t, M)):
            return None, f"node {k}: value"
        tab.append((t, ph))
    r = cert["root"]
    if r >= len(tab):
        return None, "root index"
    R = c * tab[r][1]
    return (R if R < 1 else None), f"root c*phi = {float(R):.8f}"


def unfolded_lines(cert):
    nodes = cert["nodes"]
    memo = {}
    for k in range(len(nodes)):
        tot = 1
        for ku, r, w in nodes[k]["steps"]:
            tot += 1 + (1 if r == 0 else 1 + memo[r - 1])
        memo[k] = tot
    return 2 + memo[cert["root"]]


def report(cert, label):
    lit, msg1 = check(cert, strict=False)
    st, msg2 = check(cert, strict=True)
    n = len(cert["nodes"]); steps = sum(len(nd["steps"]) for nd in cert["nodes"])
    cn, cd = cert["c"]
    print(f"{label}: c = {cn}/{cd} = {cn / cd:.10g}, d = {cert['d']}, M = 2^{cert['M'].bit_length() - 1}"
          f"{'' if cert['M'] == 1 << (cert['M'].bit_length() - 1) else ' (not a power of 2)'}, SH = {cert['SH']}, "
          f"{n} nodes, {steps} speedup steps, root {cert['root']}")
    print(f"  literal (HD.dagCheck):  {'ACCEPT' if lit is not None else 'REJECT'}  {msg1}")
    print(f"  strict  (HDS.dagCheck): {'ACCEPT' if st is not None else 'REJECT'}  {msg2}")
    t = cert["nodes"][cert["root"]]["t"]
    print(f"  normal-form proof built by nf_of_SC: from DTIME_d[n^a0], a0 = t_root = {t} ~ {t:.4e}, "
          f"to DTIME_d[n^a'] with a' <= c*phi_root*a0")
    print(f"  unfolded derivation: {unfolded_lines(cert):.4e} lines")
    return lit is not None and st is not None


def main(argv):
    ok = True
    js = None
    if "--json" in argv:
        i = argv.index("--json"); js = argv[i + 1]; argv = argv[:i] + argv[i + 2:]
    lean = [parse_lean(p) for p in argv]
    for p, cert in zip(argv, lean):
        ok &= report(cert, p)
    if js:
        cert = json.load(open(js))
        cert["nodes"] = [dict(t=n["t"], p=n["p"], phi=n["phi"], steps=[tuple(s) for s in n["steps"]]) for n in cert["nodes"]]
        ok &= report(cert, js)
        same = [p for p, L in zip(argv, lean) if L["nodes"] == cert["nodes"] and L["root"] == cert["root"]
                and L["c"] == list(cert["c"]) and (L["d"], L["M"], L["SH"]) == (cert["d"], cert["M"], cert["SH"])]
        print(f"  identical to the Lean data of: {', '.join(same) if same else 'none'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
