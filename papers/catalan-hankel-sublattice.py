#!/usr/bin/env -S uv run --quiet --with sympy --with mpmath python3
"""Jump 3, sharpened: the Hankel ledger is a SUBLATTICE problem, not a basis-search problem.

Setup (codex, papers/catalan-jump-plan.md).  With

    mu_n = int_0^1 x^(2n)(-log x)/(1+x^2) dx = (-1)^n ( G - sum_{j<n} (-1)^j/(2j+1)^2 ),

the Hankel matrix M = (mu_(i+j)) is a Gram matrix of a positive measure, so H_m = det M > 0:
**nonvanishing is free**, which is exactly the property the annihilation probe says a route to G
needs (papers/catalan-annihilation-margin.md).  M = A + G*B with B = u u^T, u_k = (-1)^k, so
H_m = A_m + B_m G is a linear form in G alone.  The naive family fails on denominators.

THE STRUCTURAL POINT.  Replacing the monomials by any integer polynomial basis p_i = sum_k U_ik t^k
gives Gram = U M U^T, hence

    det Gram = det(U)^2 * H_m.

So a UNIMODULAR change of basis leaves the numerator exactly invariant: "search over polynomial
bases" is vacuous on its own.  The G-part stays rank one for every U (it is (Uu)(Uu)^T), so
positivity and the linear-form-in-G-alone structure are basis-independent too.

What is NOT invariant is the DENOMINATOR.  Clearing det(U M U^T) costs the denominators of
U A U^T, and a non-unimodular U -- a sublattice of index D = |det U| -- can reduce them.  The trade
is asymmetric in m:

    numerator cost   = 2 log|det U|            (squared, m-independent)
    denominator gain = up to m * log(delta)    (the clearance enters the determinant as a power)

so for large m a sublattice that shrinks the per-entry denominator by any fixed factor beats the
index cost.  That is the only place a win can live, and it is the exact analogue of the
index-versus-deficit question in codex's Jump 1.

THIS PROBE measures, exactly: ledger(U) = log10( D(U) * |det Gram(U)| ), where D(U) is the true
reduced clearance lcm(den A, den B) of det Gram = A + B*G.  Baseline U = I reproduces the naive
family.  Families tried are those that could plausibly clear the (2j+1)^2 denominators.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import gcd, log10
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 400


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def rational_parts(count: int) -> list[Q]:
    """a_n with mu_n = a_n + (-1)^n G."""
    parts, partial = [], Q(0)
    for n in range(count):
        parts.append(((-1) ** (n + 1)) * partial)
        partial += Q((-1) ** n, (2 * n + 1) ** 2)
    return parts


def gram(U: sp.Matrix, m: int):
    """Exact (A, B) with det(U M U^T) = A + B*G.

    M = A + G*u u^T with u_k = (-1)^k, so by the matrix determinant lemma

        det(U M U^T) = det(X) + G * v^T adj(X) v,     X = U A U^T,  v = U u,

    which needs no symbolic variable — two exact rational linear-algebra calls instead of a
    symbolic Berkowitz determinant.  (This is also the cleanest proof that the G-part is rank one
    for every U, hence that positivity and linearity-in-G-alone are basis-independent.)
    """
    cols = U.cols
    a = rational_parts(2 * cols)
    Am = sp.Matrix(cols, cols, lambda k, l: sp.Rational(a[k + l].numerator, a[k + l].denominator))
    u = sp.Matrix(cols, 1, lambda k, _: (-1) ** k)
    X = U * Am * U.T
    v = U * u
    dX = X.det(method='bareiss')
    if dX == 0:
        return sp.Rational(0), sp.Rational(0)
    B_m = dX * (v.T * X.solve(v))[0, 0]          # v^T adj(X) v = det(X) * v^T X^{-1} v
    return sp.Rational(dX), sp.Rational(B_m)


def gram_weighted(U: sp.Matrix, w: list[int]):
    """Christoffel transform: multiply the measure by w(t) = sum_k w_k t^k >= 0 on [0,1].

    This is the ONE family the det(U M U^T) invariance does not cover, because it changes the
    measure rather than the basis.  Entries M'_ij = sum_k w_k mu_(i+j+k); the G-part is
    (-1)^(i+j) * w(-1), still RANK ONE, and positivity survives whenever w >= 0 on [0,1].
    """
    cols = U.cols
    deg = len(w) - 1
    a = rational_parts(2 * cols + deg + 2)
    Am = sp.Matrix(cols, cols, lambda i, j: sum(
        w[k] * sp.Rational(a[i + j + k].numerator, a[i + j + k].denominator)
        for k in range(deg + 1)))
    wm1 = sum(w[k] * (-1) ** k for k in range(deg + 1))
    u = sp.Matrix(cols, 1, lambda k, _: (-1) ** k)
    X = U * Am * U.T
    v = U * u
    dX = X.det(method='bareiss')
    if dX == 0 or wm1 == 0:
        return sp.Rational(0), sp.Rational(0)
    B_m = wm1 * dX * (v.T * X.solve(v))[0, 0]
    return sp.Rational(dX), sp.Rational(B_m)


def ledger(U: sp.Matrix, m: int, tag: str, w: list[int] | None = None):
    A_m, B_m = gram(U, m) if w is None else gram_weighted(U, w)
    D = lcm(int(sp.Rational(A_m).q), int(sp.Rational(B_m).q))
    G = mp.catalan
    val = mp.mpf(int(sp.Rational(A_m).p)) / int(sp.Rational(A_m).q) \
        + (mp.mpf(int(sp.Rational(B_m).p)) / int(sp.Rational(B_m).q)) * G
    if val == 0:
        print(f"  m={m:2d} {tag:28s} det = 0 (degenerate)")
        return None
    lh = float(mp.log10(abs(val)))
    ld = log10(D) if D > 0 else 0.0
    du = sp.Rational(U.det())
    idx = f"{du}" if du.q != 1 else f"{int(du)}"
    print(f"  m={m:2d} {tag:28s} log10|H|={lh:9.2f}  log10 D={ld:9.2f}  "
          f"LEDGER={lh + ld:9.2f}   det U={idx}")
    return lh + ld


def U_monomial(m):
    return sp.eye(m)


def U_falling(m):
    """rows = falling factorials t(t-1)...(t-k+1)/k!  — unimodular over Z? (integer-valued basis)"""
    t = sp.symbols('t')
    rows = []
    for k in range(m):
        poly = sp.expand(sp.prod([t - j for j in range(k)]) / sp.factorial(k))
        rows.append([sp.Poly(poly, t).coeff_monomial(t ** j) for j in range(m)])
    return sp.Matrix(rows)


def U_oddclear(m, c):
    """rows = prod_{j<k} (2t + 2j + 1) — the factors whose squares are the mu denominators.
    Non-unimodular: an index-heavy sublattice that could clear (2j+1)^2."""
    t = sp.symbols('t')
    rows = []
    for k in range(m):
        poly = sp.expand(sp.prod([2 * t + 2 * j + 1 for j in range(min(k, c))]))
        poly = sp.expand(poly * t ** max(0, k - c))
        rows.append([sp.Poly(poly, t).coeff_monomial(t ** j) if poly.has(t) or j == 0 else 0
                     for j in range(m)])
    return sp.Matrix(m, m, lambda i, j: rows[i][j])


def U_legendre(m):
    """rows = shifted Legendre P_k(2t-1) — integer coefficients, leading C(2k,k).
    The classical Beukers/Apery denominator-clearing lattice."""
    t = sp.symbols('t')
    rows = []
    for k in range(m):
        poly = sp.expand(sp.legendre(k, 2 * t - 1))
        pp = sp.Poly(poly, t)
        rows.append([pp.coeff_monomial(t ** j) for j in range(m)])
    return sp.Matrix(m, m, lambda i, j: rows[i][j])


if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[1:]] or [4, 6, 8, 10]
    print("Hankel sublattice ledger  (need LEDGER -> -infinity)")
    for m in ms:
        ledger(U_monomial(m), m, "monomial (baseline)")
        # Christoffel transforms by t^a (1-t)^b  (>= 0 on [0,1], so positivity survives)
        for (aa, bb) in ((0, 1), (0, 2), (1, 1), (0, 4)):
            w = [0] * aa + [int(sp.binomial(bb, k) * (-1) ** k) for k in range(bb + 1)]
            for Uf, nm in ((U_monomial(m), "mono"), (U_falling(m), "fall")):
                ledger(Uf, m, f"Christoffel t^{aa}(1-t)^{bb} /{nm}", w)
        try:
            Uf = U_falling(m)
            ledger(Uf, m, "falling factorial")
        except Exception as e:
            print(f"  m={m:2d} falling factorial: {e}")
        try:
            ledger(U_legendre(m), m, "shifted Legendre")
        except Exception as e:
            print(f"  m={m:2d} shifted Legendre: {e}")
        for c in (2, 4):
            try:
                ledger(U_oddclear(m, c), m, f"odd-clearing sublattice c={c}")
            except Exception as e:
                print(f"  m={m:2d} odd-clearing c={c}: {e}")
        print()
