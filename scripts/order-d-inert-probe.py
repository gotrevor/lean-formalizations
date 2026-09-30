#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Order-d generalization of the sign flip (Theorem A candidate), 2026-09-30.

Claim: if the charpoly f of A in M_d(Z) is irreducible mod the prime c, then
  sum_{i<d} A^(c^(n+i)) = (scalar) * I  (mod c^(n+1)),
because Frobenius permutes the eigenvalues cyclically and the orbit sum is a field trace.
So an off-diagonal entry u(N) = (A^N)_{ij} satisfies sum_{i<d} u(c^(n+i)) = 0 (mod c^(n+1)).

Also: survivor test.  The GL_d filter forces p_n^i = 1 (mod c^~) for some i <= d, i.e.
p_n -> a root of unity of order <= d inside Z_c.  We list h surviving that test."""
import itertools, sympy
from sympy import Poly, symbols, GF

X = symbols('X')

def matmul(A, B, m):
    d = len(A)
    return [[sum(A[i][k]*B[k][j] for k in range(d)) % m for j in range(d)] for i in range(d)]

def matpow(A, e, m):
    d = len(A); R = [[int(i == j) for j in range(d)] for i in range(d)]
    A = [[x % m for x in r] for r in A]
    while e:
        if e & 1: R = matmul(R, A, m)
        A = matmul(A, A, m); e >>= 1
    return R

def companion(coeffs):  # coeffs = [a_0, ..., a_{d-1}] with X^d = a_{d-1} X^{d-1} + ... + a_0
    d = len(coeffs)
    C = [[0]*d for _ in range(d)]
    for j in range(d): C[0][j] = coeffs[d-1-j]
    for i in range(1, d): C[i][i-1] = 1
    return C

def irreducible_mod(coeffs, c):
    d = len(coeffs)
    f = X**d - sum(coeffs[k]*X**k for k in range(d))
    return Poly(f, X, modulus=c).is_irreducible

def orbit_sum_check(C, c, K=6):
    d = len(C); m = c**K
    ok = True
    for n in range(K - 1, K + 3):
        S = [[0]*d for _ in range(d)]
        for i in range(d):
            P = matpow(C, c**(n+i), m)
            S = [[(S[r][s] + P[r][s]) % m for s in range(d)] for r in range(d)]
        mod = c**min(n+1, K)
        scalar = all(S[r][s] % mod == 0 for r in range(d) for s in range(d) if r != s) and \
                 all((S[r][r] - S[0][0]) % mod == 0 for r in range(d))
        ok &= scalar
    return ok

def roots_of_unity_mod(c, K, d):
    m = c**K
    return {x for x in range(m) if any(pow(x, i, m) == 1 for i in range(1, d+1))}

def survivors(C, c, entry, K=6):
    m = c**K; d = len(C)
    vals = [matpow(C, c**n, m)[entry[0]][entry[1]] for n in range(3*K, 3*K + 2*d + 2)]
    mu = roots_of_unity_mod(c, K // 2, d) if c**(K//2) < 10**6 else None
    mod = c**(K//2)
    hs = [h for h in range(-mod//2, mod//2) if all((v + h) % mod in mu for v in vals)]
    return hs

if __name__ == "__main__":
    # coefficient lists are [a_0, ..., a_{d-1}] for X^d = a_{d-1} X^{d-1} + ... + a_0
    fams = {"tribonacci x^3-x^2-x-1": [1, 1, 1], "plastic x^3-x-1": [1, 1, 0],
            "x^3-2x^2+x-3": [3, -1, 2], "x^3-3x^2+x-2": [2, -1, 3],
            "tetranacci": [1, 1, 1, 1], "cyclic x^3-3x+1": [-1, 3, 0],
            "x^5-x-1": [1, 1, 0, 0, 0]}
    for name, co in fams.items():
        C = companion(co); d = len(co)
        for c in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
            if not irreducible_mod(co, c): continue
            os_ok = orbit_sum_check(C, c)
            hs = survivors(C, c, (0, d-1))
            print(f"{name:20s} c={c:>2} inert: orbit-sum scalar={os_ok}; entry(0,{d-1}) survivors h mod c^3: {hs}")
