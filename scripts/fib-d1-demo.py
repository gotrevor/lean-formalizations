#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Theorem C demo (2026-09-30): Dubickas's (D1) for the NON-reversible index sequence 2^n, Fibonacci.
For H, find m such that for every |h| <= H, F(2^m)+h has a prime factor p_h with
v_2(ord_{p_h}(A)) <= m; then with L = lcm of j_h = ord of 2 modulo the odd part of ord_{p_h}(A),
p_h | F(2^(m+kL)) + h for all k >= 0.  Verified for k = 1..3 by modular exponentiation."""
import sys
from math import lcm
from sympy import factorint, n_order

def fibmod(N, p):
    def f(n):
        if n == 0: return (0, 1)
        a, b = f(n >> 1); c = a * ((2 * b - a) % p) % p; d = (a * a + b * b) % p
        return (d, (c + d) % p) if n & 1 else (c, d)
    return f(N)[0]

def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a

def matorder(p):
    # order of A = [[1,1],[1,0]] mod p (Pisano period of p): smallest k with F(k) = 0, F(k+1) = 1
    from sympy import divisors
    cand = p - 1 if p % 5 in (1, 4) else 2 * (p + 1)
    if p == 5: cand = 20
    if p == 2: cand = 3
    for d in divisors(cand):
        if fibmod(d, p) == 0 and fibmod(d + 1, p) == 1: return d
    raise ValueError(p)

def v2(x): return (x & -x).bit_length() - 1

H = int(sys.argv[1]) if len(sys.argv) > 1 else 3
for m in range(3, 12):
    ok, data = True, {}
    for h in range(-H, H + 1):
        N = fib(2 ** m) + h
        good = None
        for p in sorted(factorint(abs(N), limit=10**6)):
            if p > 10**6 or p == 5: continue
            o = matorder(p)
            if v2(o) <= m:
                odd = o >> v2(o); good = (p, n_order(2, odd) if odd > 1 else 1); break
        if good is None: ok = False; break
        data[h] = good
    if ok:
        L = lcm(*[j for _, j in data.values()])
        checks = all(fibmod(2 ** (m + k * L), p) == (-h) % p for h, (p, _) in data.items() for k in (1, 2, 3))
        print(f"H={H}: m={m}, L={L}, primes={ {h: p for h, (p, _) in data.items()} }, verified k=1..3: {checks}")
        break
    else:
        print(f"m={m}: some h had no small good prime factor (limit 1e6)")
