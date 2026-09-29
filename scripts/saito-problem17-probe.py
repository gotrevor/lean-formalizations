#!/usr/bin/env -S uv run --quiet python3
"""Saito arXiv:2504.14968 Problem 1.7 probe: does some non-reversible exponent sequence R(n)
defeat the prime-as-modulus obstruction for EVERY cubic Pisot alpha?

Why Fibonacci (Problem 1.8) fell: the tracked quantity oscillated 2-adically (an ENTRY of A^(2^n),
not Frobenius-invariant).  For floor(alpha^R(n)) = tr C^R(n) + e_n (e_n in {0,-1}) with R(n)=c^n,
the Gauss congruence makes tr C^(c^n) converge c-adically, so residual classes survive.

Test: for cubic companion matrices C mod 2^K and 3^K, R(n) = 2^n + 3^n (non-reversible, a0 = -6).
The trick forces p_n = floor(alpha^R(n)) to satisfy p_n^i = 1 mod 2^~n or mod 3^~n (i <= 3),
i.e. p_n = +-1 in Z_2 or Z_3.  We list which charpoly classes mod 8 and mod 9 have
tr C^R(n) + e in {+-1} along both parities of n (survivors = trick silent)."""
import itertools

def matmul(A, B, m):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) % m for j in range(3)] for i in range(3)]

def matpow(A, e, m):
    R = [[int(i == j) for j in range(3)] for i in range(3)]
    while e:
        if e & 1: R = matmul(R, A, m)
        A = matmul(A, A, m); e >>= 1
    return R

def comp(a, b, c):  # x^3 = a x^2 + b x + c
    return [[a, b, c], [1, 0, 0], [0, 1, 0]]

def tr_seq(C, m, ns):
    return [sum(matpow(C, 2**n + 3**n, m)[i][i] for i in range(3)) % m for n in ns]

for (q, K) in [(2, 10), (3, 6)]:
    m = q**K
    ns = range(2 * K, 2 * K + 12)
    surv = total = 0
    for a, b, c in itertools.product(range(q**2), repeat=3):
        if c % q == 0: continue  # det must be a unit mod q (p does not divide det)
        total += 1
        t = tr_seq(comp(a, b, c), m, ns)
        mod = q**(K // 2)
        ok = all(any((x + e) % mod in (1, mod - 1) for e in (0, -1)) for x in t)
        surv += ok
    print(f"q={q}: classes mod {q}^2 surviving the {q}-adic +-1 test along R(n)=2^n+3^n: {surv}/{total}")
