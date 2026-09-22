#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Direct p-adic test of Lemma 3.2 in Fauzan 2026 (Zenodo 22826419): the distribution formula

    τ_X(g) = p^{-4} Σ_{a=0}^{p-1} τ_Y^ext( g(a + p x) ),     Y = p^5 X + C_p,

for g = 1/(x - r), where τ_X(x^k) = k(k-1)(k-2) B_{k-3}/24 and τ_X(1/(x-r)) = H^{(5)}_{d(r)} - X,
d(r) = r (r ≥ 0), -r-1 (r < 0).  Far poles (a ≢ r mod p) use the Tate-algebra expansion (3.5)
    τ(1/(z - s)) = -(1/4) Σ_k C(k+3,3) B_k s^{-k-4}        (v_p(s) < 0),
and C_p = Σ_{a=1}^{p-1} τ^an(1/(x + a/p)).  B_1 = -1/2.

Lemma 3.2 carries the whole inner range (Prop 4.1), which no determinant computation can reach.
This checks it as an identity: the X-free part of the right side must equal H^{(5)}_{d(r)} to
high p-adic precision.  Controls: g = x^k (Bernoulli multiplication) and a deliberately wrong
convention (B_1 = +1/2) which must FAIL.

Usage: fauzan-zeta5-distribution-check.py [p]
"""
import sys
from fractions import Fraction as Fr
from math import comb
from sympy import bernoulli

p = int(sys.argv[1]) if len(sys.argv) > 1 else 7
KMAX = 60  # series truncation; term k has p-adic valuation ≥ k+3

def B(k, b1):
    if k == 1:
        return b1
    return Fr(int(bernoulli(k).p), int(bernoulli(k).q))

def vp(q):
    if q == 0:
        return 10 ** 9
    v = 0; n, d = q.numerator, q.denominator
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v

def H5(m):
    return sum(Fr(1, v ** 5) for v in range(1, m + 1))

def d(r):
    return r if r >= 0 else -r - 1

def tau_mono(k, b1):  # τ(x^k)
    return Fr(k * (k - 1) * (k - 2), 24) * B(k - 3, b1) if k >= 3 else Fr(0)

def tau_far(s, b1):  # τ(1/(z - s)) for v_p(s) < 0, by (3.5)
    return -Fr(1, 4) * sum(comb(k + 3, 3) * B(k, b1) * s ** (-k - 4) for k in range(KMAX))

def Cp(b1):
    return sum(tau_far(Fr(-a, p), b1) for a in range(1, p))

def rhs_pole(r, b1):
    """X-free part of p^{-4} Σ_a τ_Y^ext(1/(a + px - r)); the X part is -X automatically."""
    a0 = r % p
    rp = (r - a0) // p
    total = Fr(0)
    for a in range(p):
        if a == a0:
            total += Fr(1, p) * (H5(d(rp)) - Cp(b1))      # (1/p)(H_{d(r')} - Y), Y's X-part dropped
        else:
            c = a - r                                      # 1/(px + c) = (1/p)·1/(x - (-c/p))
            total += Fr(1, p) * tau_far(Fr(-c, p), b1)
    return total / p ** 4

def rhs_mono(k, b1):
    tot = Fr(0)
    for a in range(p):
        for i in range(k + 1):
            tot += comb(k, i) * a ** (k - i) * p ** i * tau_mono(i, b1)
    return tot / p ** 4

print(f"p = {p}, truncation K={KMAX}, B_1 = -1/2 (paper's convention)")
print("controls, g = x^k (Bernoulli multiplication):")
for k in (3, 4, 6, 9):
    print(f"  k={k}: v_p(LHS-RHS) = {vp(tau_mono(k, Fr(-1,2)) - rhs_mono(k, Fr(-1,2)))}")
print("poles, g = 1/(x - r):  v_p( RHS_const - H5_{d(r)} )   (large = identity holds to that precision)")
for r in (0, 1, 2, 3, 6, 10, 23, -1, -2, -5, -12):
    v = vp(rhs_pole(r, Fr(-1, 2)) - H5(d(r)))
    print(f"  r={r:>4}  d(r)={d(r):>3}   v_p = {v}")
print("negative control, B_1 = +1/2 (must fail):")
for r in (1, 3):
    print(f"  r={r}: v_p = {vp(rhs_pole(r, Fr(1, 2)) - H5(d(r)))}")
print(f"v_p(C_p) = {vp(Cp(Fr(-1,2)))}  (paper: C_p ∈ p^5 Z_p)")
