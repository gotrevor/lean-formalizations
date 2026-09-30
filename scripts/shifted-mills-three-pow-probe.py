#!/usr/bin/env -S uv run --quiet python3
"""Phase 59 probe: the hypotheses of `xi_shifted_three_pow_transcendental`.

C_k = 3^(k+j) + 3^a * s' with s' even, 3 ∤ s', s' ≥ 8, and 3^a s' ≤ 3^(j+1).
Checks, for every such (a, s') in a range and the least admissible j:
  1. a < j (so C_m = 3^a (3^(m+j-a) + s') with a positive inner exponent);
  2. (B5') C_m | C_(m+t) for t = ord_(C_m / 3^a)(3), m = 1..6 (C_m itself is divisible by 3,
     so Euler on C_m is unavailable; the reduction to D_m = C_m / 3^a is what works);
  3. the eventual common divisor of odd C_k is exactly 3^a (so Saito's g is 3^b, b <= a);
  4. size: κ^(s'·3^(a-b)) > 4 for every b <= a (the smallest exponent is s').
Controls that must FAIL:
  A. s' = 4: κ^4 < 4 (size fails, Theorem D gives nothing);
  B. Euler on C_m directly: 3^φ(C_m) ≢ 1 mod C_m when a ≥ 1.
"""
from math import gcd

KAPPA = 1.324717957244746  # plastic number, κ^3 = κ + 1


def ord3(n: int) -> int:
    t, x = 1, 3 % n
    while x != 1 % n:
        x = x * 3 % n
        t += 1
    return t


def phi(n: int) -> int:
    r, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            r -= r // p
        p += 1
    if m > 1:
        r -= r // m
    return r


cases = fails = 0
for a in range(0, 4):
    for sp in range(8, 60, 2):
        if sp % 3 == 0:
            continue
        s = 3**a * sp
        j = 0
        while s > 3 ** (j + 1):
            j += 1
        C = lambda k: 3 ** (k + j) + s
        cases += 1
        ok = a < j
        for m in range(1, 7):
            D = C(m) // 3**a
            ok &= C(m) % 3**a == 0 and D % 3 != 0
            t = ord3(D)
            ok &= C(m + t) % C(m) == 0
        g = 0
        for k in range(20, 26):
            g = gcd(g, C(k))
        ok &= g == 3**a
        ok &= KAPPA ** sp > 4
        if not ok:
            fails += 1
            print("FAIL", a, sp, j)
print(f"{cases} cases, {fails} failures")
assert fails == 0

# Control A: s' = 4 violates the size bound.
assert KAPPA**4 < 4, "control A should fail the size bound"
# Control B: Euler on C_m directly is unavailable once 3 | C_m.
a, sp = 1, 8
s = 3**a * sp
j = 2
Cm = 3 ** (1 + j) + s
assert pow(3, phi(Cm), Cm) != 1, "control B should fail"
print("controls fail as they should")
