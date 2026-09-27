#!/usr/bin/env -S uv run --quiet --with mpmath --with sympy python3
"""Inner-range heuristic for Fauzan 2026 (Zenodo 22826419).

Prop 4.1 (K/M < p ≤ K/3) needs K ≥ 200M^2 ≥ 320000 and cannot be instantiated at any K where
Δ_K is computable.  Its asymptotic content is (5.7): γ_p^in = p·Γ(K/p) + O_M(1).  This prints
p·Γ(K/p) for the primes p ≤ K/3 at a small K so it can be set beside the exact v_p^G(Δ_K) from
fauzan-zeta5-hankel-probe.py.  Agreement is evidence about the mechanism, not a proof of Prop 4.1.

Usage: fauzan-zeta5-inner-heuristic.py K
"""
import sys
import mpmath as mp
from sympy import primerange

mp.mp.dps = 30
alpha = mp.mpf(3) / 40; lam = mp.mpf(37) / 40; H = 1 + 2 * alpha
K = int(sys.argv[1])

def ell(x, z): return mp.floor(x - z) + mp.floor(x + z) + 1

def Gamma(x):  # (5.4)
    T = mp.floor(2 * H * x); s = H * x - T / 2; q = mp.floor(2 * x); nplus = (2 * x - q) / 2
    bps = set([mp.mpf(0), mp.mpf(1) / 2])
    for y in (x, alpha * x):
        for k in range(int(mp.floor(y)) - 1, int(mp.floor(y)) + 3):
            for z in (y - k, k - y):
                if 0 < z < mp.mpf(1) / 2: bps.add(z)
    bps = sorted(bps)
    G = mp.mpf(0)
    for lo, hi in zip(bps, bps[1:]):
        z = (lo + hi) / 2
        bz = 3 * ell(alpha * x, z); lz = ell(x, z)
        G += (T - bz) * (T + bz - lz - 5) * (hi - lo)
    return G + s * (2 * T - q - 5) + max(s - nplus, 0)

print(f"K={K}: inner primes p ≤ K/3 with the (5.7) prediction p·Γ(K/p) for γ_p^in")
for p in primerange(2, K // 3 + 1):
    x = mp.mpf(K) / p
    print(f"{p:>5}  x=K/p={mp.nstr(x,5):>7}  pΓ(x)={mp.nstr(p*Gamma(x),6):>9}")
