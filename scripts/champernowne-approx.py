#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Champernowne C10 = 0.123456789101112...: the rational approximations Mahler/Roth use.

After the (k-1)-digit numbers end (N digits), the k-digit block a, a+1, ... (a = 10^(k-1)) is the
start of sum_{j>=0} (a+j) x^(j+1), x = 10^-k, which is the rational a x/(1-x) + x^2/(1-x)^2.
So p/q with q = 10^N (10^k - 1)^2 should match C to about N + 9k*10^(k-1) digits.
Prints the effective exponent  -log|C - p/q| / log q  (Roth needs > 2)."""
from fractions import Fraction
from mpmath import mp, mpf, log
K = 4
digits = "".join(str(n) for n in range(1, 10 ** K + 50))
mp.dps = len(digits) + 20
C = mpf("0." + digits)
for k in range(2, K + 1):
    N = sum(9 * d * 10 ** (d - 1) for d in range(1, k))
    a, x = 10 ** (k - 1), Fraction(1, 10 ** k)
    tail = a * x / (1 - x) + x * x / (1 - x) ** 2
    approx = Fraction(int(digits[:N]), 10 ** N) + tail / 10 ** N
    q = approx.denominator
    err = abs(C - mpf(approx.numerator) / approx.denominator)
    print(f"k={k} N={N} log10 q={float(log(q,10)):.1f} -log10 err={float(-log(err,10)):.1f} "
          f"exponent={float(log(err) / -log(q)):.2f}")
