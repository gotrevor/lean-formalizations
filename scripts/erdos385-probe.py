#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Probe for Erdős #385 / #430.

F(n) = max{ m + lpf(m) : m < n composite }.  #385(i): F(n) > n eventually (== #430).
Equivalently: g(n) := least a >= 1 with n - a composite and lpf(n - a) > a exists.

Prints, for n <= N:
  * record values of g(n) (the "first good distance"), with n's factorization
    and whether n - 1 is prime;
  * the minimum of F(n) - n and of (F(n) - n)/sqrt(n) over dyadic blocks (#385(ii), lb).

Usage: erdos385-probe.py [N]   (default 10**7)
"""
import math
import sys

import numpy as np

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7


def lpf_sieve(n):
    lpf = np.zeros(n + 1, dtype=np.int64)
    for p in range(2, int(n**0.5) + 1):
        if lpf[p] == 0:
            block = lpf[p * p :: p]
            block[block == 0] = p
    idx = np.arange(n + 1)
    mask = (lpf == 0) & (idx >= 2)
    lpf[mask] = idx[mask]
    return lpf


def factor(n, lpf):
    out = []
    while n > 1:
        p = int(lpf[n])
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append(f"{p}^{e}" if e > 1 else str(p))
    return "·".join(out)


lpf = lpf_sieve(N)
idx = np.arange(N + 1)
composite = (lpf < idx) & (idx >= 4)

# g(n): iterate a upward, resolving n where m = n - a is composite with lpf(m) > a.
g = np.zeros(N + 1, dtype=np.int64)
unresolved = idx >= 5
a = 0
while unresolved.any():
    a += 1
    m = idx - a
    ok = np.zeros(N + 1, dtype=bool)
    valid = m >= 4
    ok[valid] = composite[m[valid]] & (lpf[m[valid]] > a)
    hit = unresolved & ok
    g[hit] = a
    unresolved &= ~hit
    if a * a > N:  # lpf(n - a) > a with n - a composite forces a < sqrt(n)
        break

fail = np.nonzero(unresolved)[0]
print(f"F(n) <= n (no good a) for {len(fail)} n in [5, N]; largest 40:")
print("  ", fail[-40:].tolist())
print("   n-1 prime for all of them?", bool(np.all(lpf[fail - 1] == fail - 1)))
for n in fail[-8:]:
    print(f"   {n} = {factor(int(n), lpf)}")

print(f"N = {N:,}; max g(n) = {g.max()} (n >= 5)")
print("records of g(n):  n | g(n) | n-1 prime? | factorization of n")
best = 0
for n in range(5, N + 1):
    if g[n] > best:
        best = g[n]
        print(f"  {n:>10} | {best:>4} | {str(lpf[n - 1] == n - 1):>5} | {factor(n, lpf)}")

# F(n) - n via prefix max of m + lpf(m) over composite m < n.
val = np.where(composite, idx + lpf, 0)
pref = np.maximum.accumulate(val)
F = np.zeros(N + 1, dtype=np.int64)
F[1:] = pref[:-1]
print("\nF(n) - n over dyadic blocks [2^k, 2^(k+1)):  min(F-n) | min((F-n)/sqrt n) | argmin")
k = 4
while 2 ** (k + 1) <= N + 1:
    lo, hi = 2**k, 2 ** (k + 1)
    d = F[lo:hi] - idx[lo:hi]
    r = d / np.sqrt(idx[lo:hi])
    j = int(np.argmin(d))
    print(f"  k={k:>2}: {int(d.min()):>6} | {r.min():.3f} | n={lo + j}")
    k += 1
