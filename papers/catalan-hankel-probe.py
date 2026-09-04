#!/usr/bin/env -S uv run --quiet --with sympy --with mpmath python3
"""Exact ledger for a positive Hankel-determinant linear form in Catalan's G.

Let

    mu_n = integral_0^1 x^(2n) (-log x)/(1+x^2) dx
         = (-1)^n (G - sum_{j=0}^{n-1} (-1)^j/(2j+1)^2).

The Hankel determinant H_m = det(mu_(i+j)) is positive.  Since the matrix of
G-coefficients is ((-1)^(i+j)) = u*u^T, it has rank one, so H_m=A_m+B_m G.
This script computes A_m and B_m exactly and tests the minimally cleared
quantity D_m H_m.  A proof by this route requires D_m H_m -> 0.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
import sys

import mpmath as mp
import sympy as sp


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def rational_parts(count: int) -> list[Fraction]:
    """Return a_n such that mu_n=a_n+(-1)^n G."""
    parts: list[Fraction] = []
    partial = Fraction(0)
    for n in range(count):
        parts.append(((-1) ** (n + 1)) * partial)
        partial += Fraction((-1) ** n, (2 * n + 1) ** 2)
    return parts


def q(value: Fraction) -> sp.Rational:
    return sp.Rational(value.numerator, value.denominator)


def exact_form(
    size: int, parts: list[Fraction], shift: int = 0
) -> tuple[Fraction, Fraction]:
    """Return A,B with det(mu_(i+j))=A+B*G."""
    base = sp.Matrix(size, size, lambda i, j: q(parts[shift + i + j]))
    signs = sp.Matrix([(-1) ** i for i in range(size)])
    a = base.det(method="domain-ge")
    at_one = (base + (-1) ** shift * signs * signs.T).det(method="domain-ge")
    b = at_one - a
    return Fraction(int(a.p), int(a.q)), Fraction(int(b.p), int(b.q))


def ledger(size: int, shift: int, parts: list[Fraction], catalan: mp.mpf):
    a, b = exact_form(size, parts, shift)
    denominator = lcm(a.denominator, b.denominator)
    value = mp.mpf(a.numerator) / a.denominator
    value += mp.mpf(b.numerator) / b.denominator * catalan
    assert value > 0
    return mp.log10(value), mp.log10(denominator), denominator


def main(max_size: int = 18, scan_shifts: bool = False) -> None:
    mp.mp.dps = 160
    catalan = mp.catalan
    max_shift = 3 * max_size if scan_shifts else 0
    parts = rational_parts(2 * max_size + max_shift)
    if scan_shifts:
        print("m best_shift log10(H) log10(D) log10(D*H)")
        for size in range(1, max_size + 1):
            rows = []
            for shift in range(0, 3 * size + 1):
                log_h, log_d, _ = ledger(size, shift, parts, catalan)
                rows.append((log_h + log_d, shift, log_h, log_d))
            score, shift, log_h, log_d = min(rows)
            print(size, shift, mp.nstr(log_h, 12), mp.nstr(log_d, 12), mp.nstr(score, 12))
        return

    print("m log10(H_m) log10(D_m) log10(D_m*H_m) Ddigits")
    for size in range(1, max_size + 1):
        log_h, log_d, denominator = ledger(size, 0, parts, catalan)
        print(
            size,
            mp.nstr(log_h, 12),
            mp.nstr(log_d, 12),
            mp.nstr(log_h + log_d, 12),
            len(str(denominator)),
        )


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "shifts":
        main(int(sys.argv[2]) if len(sys.argv) > 2 else 10, scan_shifts=True)
    else:
        main(int(sys.argv[1]) if len(sys.argv) > 1 else 18)
