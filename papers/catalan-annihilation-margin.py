#!/usr/bin/env -S uv run --quiet --with sympy --with mpmath --with numpy python3
"""Annihilation-margin probe: what does killing beta(4..s-1) cost in the ledger?

Zudilin's s-fold construction (Phase 4, DIRECTION.md) produces

    r_n = A_0 + sum_{i even, 2<=i<=s-1} A_i beta(i),

a WIDE beam: all (s-1)/2 even beta values appear, which is why the theorem is only a
disjunction.  A construction that annihilated A_4,...,A_{s-1} would leave

    r_n = A_0 + A_2 * G,

a linear form in Catalan's constant ALONE -- i.e. G irrational, if the ledger still closes.
Zudilin's "twist by half" does exactly this kind of annihilation for odd zeta values in his
SIGMA 2018 paper, so the question is not idle.

THE FAMILY.  R_n(-t-n) = R_n(t) holds because the prefactor (2t+n) is ANTIsymmetric under
t -> -t-n and the rest of R_n contributes a compensating sign.  So the arithmetic-preserving
deformations that keep the odd-i vanishing are exactly

    Q(t) = sum_{k=0}^{K} c_k * (2t+n)^(2k+1),        c_k in Z,

with the SAME denominator prod_{j=0}^{n}(t+j)^s -- hence the same d_n^s clearance for every
basis element, so integer combinations stay integral.  (The probe MEASURES the clearance
rather than assuming it.)

WHAT IS MEASURED.  For each s: build the basis, get each A_i exactly by partial fractions,
solve the ((s-1)/2 - 1) linear conditions A_4 = ... = A_{s-1} = 0 over Q, clear a primitive
integer kernel vector c, and report the ledger of the resulting form a + b*G against the
ledger of Zudilin's own r_n:

    ledger := ( log|r_n(c)| + s*log(d_n) + log(height(c)) ) / n      [want -> -infinity]
    Delta  := ledger(annihilated) - ledger(full)                     [the COST of the beam]

The interesting output is not "does it work" (it does not) but the SHAPE of Delta vs s.
Zudilin's own margin improves ~0.39 per unit s (papers/catalan-beta-ledger.py).  If Delta is
bounded in s, there is a crossover; if Delta grows faster than 0.39/unit-s, the beam is not
narrowable this way and the family is dead for the prize.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import lcm
import sys

import mpmath as mp
import numpy as np
import sympy as sp

t = sp.symbols('t')
mp.mp.dps = 60


def dn(n: int) -> int:
    L = 1
    for k in range(1, n + 1):
        L = lcm(L, k)
    return L


def beta(i: int):
    return mp.nsum(lambda k: (-1) ** int(k) / (2 * k + 1) ** i, [0, mp.inf])


def R_basis(n: int, s: int, k: int):
    """Basis element k: Zudilin's R_n with (2t+n) replaced by (2t+n)^(2k+1)."""
    num = (2 ** (6 * n) * sp.factorial(n) ** (s - 3) * (2 * t + n) ** (2 * k + 1)
           * sp.prod([t - n + j - sp.Rational(1, 2) for j in range(1, 3 * n + 1)]))
    den = sp.prod([(t + j) ** s for j in range(0, n + 1)])
    return num / den


def decompose(R, n: int, s: int):
    """Return (A dict i->Fraction, A0 Fraction, max denominator of d_n^s * coeffs)."""
    pf = sp.apart(sp.cancel(R), t)
    a: dict[tuple[int, int], Q] = {}
    for term in sp.Add.make_args(pf):
        c, rest = term.as_coeff_Mul()
        b, e = rest.as_base_exp()
        if e >= 0:                      # polynomial part: must be absent (degree condition)
            assert sp.simplify(term) == 0, f"non-decaying part {term}"
            continue
        k = int(b.subs(t, 0))
        i = int(-e)
        a[(i, k)] = a.get((i, k), Q(0)) + Q(str(sp.nsimplify(c)))
    m = n // 2

    def S(i: int, k: int):
        sgn = -1 if (k - 1) % 2 else 1
        lo = k - m - 2
        rat = Q(0)
        if lo < 0:
            for l in range(lo, 0):
                j = -l - 1
                rat += Q((-1) ** (j + 1) * (-1) ** i) / (Q(2 * j + 1, 2) ** i)
        else:
            for l in range(0, lo):
                rat -= Q((-1) ** l) / (Q(2 * l + 1, 2) ** i)
        return sgn, Q(sgn) * rat

    A: dict[int, Q] = {}
    A0 = Q(0)
    for (i, k), c in a.items():
        sgn, rat = S(i, k)
        A[i] = A.get(i, Q(0)) + c * sgn * 2 ** i
        A0 += c * rat
    D = dn(n) ** s
    clear = max([(A[i] * D).denominator for i in A] + [(A0 * D).denominator])
    return A, A0, clear


def lll_reduce(Qm, delta=0.99):
    """LLL on Z^d with positive-definite float quadratic form Qm; returns the unimodular U
    whose ROWS are the reduced basis in coefficient coordinates."""
    d = Qm.shape[0]
    Bm = np.linalg.cholesky(Qm).T
    U = np.eye(d, dtype=object)

    def gso(Bm):
        Bs = np.zeros_like(Bm)
        mu = np.zeros((d, d))
        for i in range(d):
            v = Bm[:, i].copy()
            for j in range(i):
                mu[i, j] = Bm[:, i] @ Bs[:, j] / (Bs[:, j] @ Bs[:, j])
                v -= mu[i, j] * Bs[:, j]
            Bs[:, i] = v
        return Bs, mu

    Bs, mu = gso(Bm)
    k = 1
    while k < d:
        for j in range(k - 1, -1, -1):
            q = int(round(mu[k, j]))
            if q != 0:
                Bm[:, k] -= q * Bm[:, j]
                U[:, k] -= q * U[:, j]
                Bs, mu = gso(Bm)
        if Bs[:, k] @ Bs[:, k] >= (delta - mu[k, k - 1] ** 2) * (Bs[:, k - 1] @ Bs[:, k - 1]):
            k += 1
        else:
            Bm[:, [k, k - 1]] = Bm[:, [k - 1, k]]
            U[:, [k, k - 1]] = U[:, [k - 1, k]]
            Bs, mu = gso(Bm)
            k = max(k - 1, 1)
    return U.T


def score(c, cols, n, s, G):
    """Exact rescoring of an integer combination: (ledger, |a+bG|, height, A2)."""
    A2 = sum((Q(int(c[k])) * cols[k][0].get(2, Q(0)) for k in range(len(c))), Q(0))
    A0 = sum((Q(int(c[k])) * cols[k][1] for k in range(len(c))), Q(0))
    height = max(abs(int(x)) for x in c)
    if height == 0:
        return None
    val = mp.mpf(A0.numerator) / A0.denominator + (mp.mpf(A2.numerator) / A2.denominator) * G
    if val == 0:
        return None
    ledger = (mp.log(abs(val)) + s * mp.log(dn(n)) + mp.log(mp.mpf(height))) / n
    return float(ledger), val, height, A2


def run(s: int, n: int, extra: int = 0) -> None:
    evens = [i for i in range(2, s) if i % 2 == 0]
    kill = evens[1:]                                   # A_4 .. A_{s-1}
    # convergence caps the deformation: deg(num) = 3n + (2k+1) <= deg(den) - 2 = s(n+1) - 2
    kmax = (s * (n + 1) - 3 * n - 3) // 2
    K = min(len(kill) + extra, kmax)                   # basis size K+1
    if K < len(kill):
        print(f"  s={s} n={n}: SKIP — convergence caps the basis at {kmax+1} < {len(kill)+1} needed")
        return
    print(f"  s={s} n={n}: {len(evens)} even beta values, killing {len(kill)}, "
          f"basis size {K+1} (cap {kmax+1}), kernel dim {K+1-len(kill)}")

    cols = []
    for k in range(K + 1):
        A, A0, clear = decompose(R_basis(n, s, k), n, s)
        cols.append((A, A0, clear))
        sys.stdout.write('.'); sys.stdout.flush()
    print()

    bad = [k for k, (_, _, c) in enumerate(cols) if c != 1]
    print(f"    d_n^s clearance holds for every basis element: {not bad}"
          + (f"  (offenders {bad})" if bad else ""))

    M = sp.Matrix([[sp.Rational(cols[k][0].get(i, Q(0)).numerator,
                               cols[k][0].get(i, Q(0)).denominator) for k in range(K + 1)]
                   for i in kill])
    ker = M.nullspace()
    if not ker:
        print("    no annihilating combination in this basis")
        return
    G = beta(2)

    # integer basis of the annihilating lattice
    V = []
    for v in ker:
        den = sp.lcm([sp.Rational(x).q for x in v])
        c = [int(sp.Rational(x) * den) for x in v]
        g = 0
        for x in c:
            g = sp.gcd(g, abs(x))
        V.append([x // int(g) for x in c] if g else c)
    d = len(V)

    def report(tag, c):
        r = score(c, cols, n, s, G)
        if r is None:
            print(f"    {tag}: degenerate")
            return None
        led, val, height, A2 = r
        print(f"    {tag}: height={height}  a+bG={mp.nstr(val, 6)}  A_2!=0:{A2 != 0}  "
              f"LEDGER={led:8.3f}")
        return led

    best = report("raw kernel vector  ", V[0])

    if d > 1:
        # LLL over the annihilating lattice, minimising |c| together with |a+bG|
        Ls = []
        for v in V:
            A2v = sum((Q(v[k]) * cols[k][0].get(2, Q(0)) for k in range(K + 1)), Q(0))
            A0v = sum((Q(v[k]) * cols[k][1] for k in range(K + 1)), Q(0))
            Ls.append(float(mp.mpf(A0v.numerator) / A0v.denominator
                            + (mp.mpf(A2v.numerator) / A2v.denominator) * G))
        Va = np.array([[float(x) for x in v] for v in V])
        sig = max(np.abs(Va).max(), 1.0)
        Lv = np.array(Ls)
        w = sig / max(np.abs(Lv).max(), 1e-300)        # equalise the two contributions
        Gram = (Va @ Va.T) / sig ** 2 + (w ** 2 / sig ** 2) * np.outer(Lv, Lv)
        Gram += np.eye(d) * 1e-9 * np.trace(Gram) / d
        try:
            U = lll_reduce(Gram)
        except Exception as e:                          # float trouble: report and move on
            print(f"    LLL failed ({e}); raw kernel vector stands")
            return
        cands = []
        for row in U:
            c = [sum(int(row[i]) * V[i][k] for i in range(d)) for k in range(K + 1)]
            r = score(c, cols, n, s, G)
            if r is not None:
                cands.append((r[0], c, r))
        if cands:
            cands.sort()
            led, c, r = cands[0]
            print(f"    LLL-reduced (dim {d}): height={r[2]}  a+bG={mp.nstr(r[1], 6)}  "
                  f"LEDGER={led:8.3f}")
            best = min(best, led) if best is not None else led

    A, A0f, _ = decompose(R_basis(n, s, 0), n, s)
    Gf = mp.mpf(A0f.numerator) / A0f.denominator + sum(
        (mp.mpf(A[i].numerator) / A[i].denominator) * beta(i) for i in A if i % 2 == 0)
    full = float((mp.log(abs(Gf)) + s * mp.log(dn(n))) / n)
    print(f"    LEDGER full-beam    = {full:8.3f}   DELTA = {best - full:+8.3f}"
          f"   (need LEDGER < 0 for G irrational)")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    extra = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    todo = [int(x) for x in sys.argv[3:]] or [7, 9, 11, 13]
    print(f"annihilation-margin probe, n={n}, extra basis vectors={extra}")
    for s in todo:
        run(s, n, extra)
