# SPDX-License-Identifier: Apache-2.0
import math, sys

def log2fact(x):
    return math.lgamma(x + 1) / math.log(2)

def params(c, L, lam=None):
    n = 2.0 ** L
    s = math.ceil(c * n) if lam is None else math.ceil(n * lam)
    sp = 3 * s
    H = n + sp
    R = 3 * H
    r = math.ceil(math.sqrt(R))
    q = math.ceil(R / r)
    Rp = r * q
    D = 4 * sp + 2 * q * math.ceil(log2fact(r)) + r * math.ceil(log2fact(q))
    b = math.ceil(L)
    t = math.ceil(n / b)
    m = math.ceil(2 * D / n)
    j = 2 * m
    kappa = math.ceil(math.log2(H + 1))
    S = D + 4 * j * n + 5 * j * sp + 8 * Rp * (kappa + j) + j
    deg = max(2 * r * (kappa + j) + math.ceil(log2fact(r)),
              2 * q * (kappa + j) + math.ceil(log2fact(q)))
    a = math.ceil(math.log2(m))
    exact = D + 2 * m * t * math.log2(m) - m * n
    return dict(n=n, s=s, D=D, m=m, t=t, S=S, deg=deg, a=a, b=b,
                exact_ok=exact < 0, lean_ok=8 * t * a <= n and 2 * D <= m * n,
                crude_ok=16 * a <= b and 16 * a <= n,
                deg_ok=deg <= math.ceil(S ** 0.9))

def first(c, key, lam=None, lo=8, hi=900):
    for L in range(lo, hi):
        if all(params(c, LL, lam)[key] for LL in range(L, min(L + 60, hi))):
            return L
    return None

if __name__ == "__main__":
    print("c | D/(cn log n) m/(c log n) S/(c^2 n log n) at log2 n = 200 | first log2 n: exact potential, Lean condition (8ta<=n), crude (16a<=b), degree")
    for c in [1, 3.5, 4, 16, 64]:
        p = params(c, 200)
        n = p["n"]
        print(c, "|", round(p["D"] / (c * n * 200), 2), round(p["m"] / (c * 200), 2),
              round(p["S"] / (c * c * n * 200), 1), "|",
              first(c, "exact_ok"), first(c, "lean_ok"), first(c, "crude_ok"), first(c, "deg_ok"))
    print("closed-form bounds check over log2 n in [threshold, 900]:")
    for c in [1, 3.5, 4, 16, 64]:
        ok = True
        for L in range(first(c, "lean_ok"), 900, 7):
            p = params(c, L)
            n = p["n"]
            ok &= p["D"] <= 25 * c * n * L and p["m"] <= 51 * c * L and p["S"] <= 1e4 * c * c * n * L
        print(c, ok)
    print("Corollary C, s = n*lam, lam = (log2 n)^(1/4): first log2 n (exact, Lean, degree)")
    for L0 in [None]:
        pass
    for L in [100, 200, 400, 800]:
        lam = L ** 0.25
        p = params(1, L, lam)
        print(L, round(lam, 2), p["exact_ok"], p["lean_ok"], p["deg_ok"], round(p["S"] / (lam * lam * p["n"] * L), 1))
