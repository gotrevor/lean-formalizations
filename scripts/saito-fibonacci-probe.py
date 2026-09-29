#!/usr/bin/env -S uv run --quiet --with sympy python3
# Problem 1.8 probe: F(2^n) mod 2^K, L(2^k)+1 valuations, and the prime-as-modulus mechanism.
def fib(n):
    def f(n):
        if n == 0: return (0, 1)
        a, b = f(n >> 1); c = a*(2*b - a); d = a*a + b*b
        return (d, c + d) if n & 1 else (c, d)
    return f(n)[0]
v2 = lambda x: (x & -x).bit_length() - 1
L = [3]  # L(2^1)=3; L(2m) = L(m)^2 - 2 for even m
for k in range(2, 13): L.append(L[-1]**2 - 2)
print("v2(L(2^k)+1), k=1..:", [v2(l + 1) for l in L])
F = [fib(2**n) for n in range(14)]
print("F(2^n) odd:", all(f % 2 for f in F[1:]))
print("v2(F(2^(n+1)) + F(2^n)):", [v2(F[n+1] + F[n]) for n in range(1, 13)])
# mechanism check: for p = F(2^n)+h prime, does p | F(2^(n+j))+h for some j?  (order of A mod p odd-part case)
from sympy import isprime
def matpow(M, e, p):
    R = [[1,0],[0,1]]
    while e:
        if e & 1: R = [[(R[0][0]*M[0][0]+R[0][1]*M[1][0])%p,(R[0][0]*M[0][1]+R[0][1]*M[1][1])%p],[(R[1][0]*M[0][0]+R[1][1]*M[1][0])%p,(R[1][0]*M[0][1]+R[1][1]*M[1][1])%p]]
        M = [[(M[0][0]*M[0][0]+M[0][1]*M[1][0])%p,(M[0][0]*M[0][1]+M[0][1]*M[1][1])%p],[(M[1][0]*M[0][0]+M[1][1]*M[1][0])%p,(M[1][0]*M[0][1]+M[1][1]*M[1][1])%p]]
        e >>= 1
    return R
for h in [-5, -3, -1, 1, 2, 3, 4, 7]:
    rows = []
    for n in range(2, 12):
        p = F[n] + h
        if p > 2 and isprime(p):
            # smallest j>0 with F(2^(n+j)) ≡ -h mod p, via A^(2^(n+j)) mod p
            hit = next((j for j in range(1, 200) if (matpow([[1,1],[1,0]], pow(2, n+j), p)[0][1] + h) % p == 0), None)
            rows.append((n, p % 2**n in (1, 2**n - 1), hit))
    print("h=%d prime n: (n, p≡±1 mod 2^n, first j with p|F(2^(n+j))+h)" % h, rows)
