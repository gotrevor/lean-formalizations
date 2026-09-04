#!/usr/bin/env -S uv run --quiet --with sympy --with mpmath python3
"""Fixed-size SHIFTED Hankel minors: the first family with all three properties.

papers/catalan-hankel-sublattice.md killed the growing-size Hankel family by a capacity-vs-lcm
inequality: an m x m determinant must reach moment index 2m, so clearing it costs e^{4m^2} against
a numerator of only e^{-(log 4)m^2}.

But that failure is about the determinant's SIZE, not about moments.  Hold m fixed and grow the
shift instead:

    M(n)_{ij} = mu_{n+i+j},   0 <= i,j < m,      H_m(n) = det M(n).

* (A) nonvanishing is still free: M(n) is the Gram matrix of the positive measure x^n dmu.
* (C) the beam stays narrow: the G-part of mu_{n+i+j} is (-1)^{n+i+j} = (-1)^n(-1)^i(-1)^j,
      rank one, so H_m(n) = A + B*G is a linear form in Catalan's constant ALONE.
* (B) the denominator index is now n + 2m - 2, LINEAR in the growing parameter, and clearing an
      m x m determinant costs that to the m-th power — an exponent linear in n, not quadratic.

So the ledger is log|H_m(n)| + m * log(denominator index growth), and both terms are linear in n.
That is a fair fight, which the growing-size family never was.  This probe measures it exactly.

Reported per (m, n): log10|H|, log10 D (the true reduced clearance of A + B*G), and their sum.
The proof condition is LEDGER -> -infinity in n at fixed m.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import gcd, log10
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 300


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def rational_parts(count: int) -> list[Q]:
    """a_n with mu_n = a_n + (-1)^n G."""
    parts, partial = [], Q(0)
    for n in range(count):
        parts.append(((-1) ** (n + 1)) * partial)
        partial += Q((-1) ** n, (2 * n + 1) ** 2)
    return parts


def shifted(m: int, n: int, a: list[Q]):
    """Exact (A, B) with det(mu_{n+i+j})_{i,j<m} = A + B*G, via the matrix determinant lemma."""
    X = sp.Matrix(m, m, lambda i, j: sp.Rational(a[n + i + j].numerator, a[n + i + j].denominator))
    v = sp.Matrix(m, 1, lambda i, _: (-1) ** i)
    dX = X.det(method='bareiss')
    if dX == 0:
        return sp.Rational(0), sp.Rational(0)
    B = ((-1) ** n) * dX * (v.T * X.solve(v))[0, 0]
    return sp.Rational(dX), sp.Rational(B)


def run(m: int, ns: list[int]) -> None:
    a = rational_parts(max(ns) + 2 * m + 2)
    G = mp.catalan
    print(f"\n  m={m} (fixed determinant size), growing shift n:")
    print(f"    {'n':>4} {'log10|H|':>11} {'log10 D':>10} {'LEDGER':>10} {'slope':>9}")
    prev = None
    for n in ns:
        A, B = shifted(m, n, a)
        if A == 0 and B == 0:
            print(f"    {n:>4}   degenerate")
            continue
        D = lcm(int(sp.Rational(A).q), int(sp.Rational(B).q))
        val = (mp.mpf(int(sp.Rational(A).p)) / int(sp.Rational(A).q)
               + (mp.mpf(int(sp.Rational(B).p)) / int(sp.Rational(B).q)) * G)
        if val == 0:
            print(f"    {n:>4}   H = 0 exactly")
            continue
        lh = float(mp.log10(abs(val)))
        ld = log10(D)
        led = lh + ld
        sl = f"{(led - prev[1]) / (n - prev[0]):+9.3f}" if prev else " " * 9
        print(f"    {n:>4} {lh:>11.3f} {ld:>10.3f} {led:>10.3f} {sl}")
        prev = (n, led)


if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[1:]] or [2, 3, 4]
    print("Shifted Hankel ledger — need LEDGER -> -infinity in n at fixed m")
    for m in ms:
        run(m, [2, 4, 8, 16, 24, 32, 48, 64])
