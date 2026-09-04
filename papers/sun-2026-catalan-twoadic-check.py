#!/usr/bin/env -S uv run --quiet python3
"""Exact rational check of the 2-adic obstruction in arXiv:2609.04176.

Assume G = a/q (the paper's hypothesis).  Build the paper's R, qhat_B, N_B
exactly over Q and read off v_2.  Claim under test:
    v_2(N_B) >= v_2(F_B) ~ 2B^2,  hence |N_B| >= 2^(2B^2)  -- not < 1.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial

def v2(x: F) -> int:
    if x == 0: return None
    n, d = x.numerator, x.denominator
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v

def run(B, S, q, a):
    G = F(a, q)
    N = 2*B + S + 3
    D = 2*B
    # tails T_m = (-1)^m (G - S_{m-1}),  u_m = T_m/(2m+1)
    maxm = (2*B + S + 2) + S + 2
    Spart = [F(0)]*(maxm+2)
    s = F(0)
    for k in range(maxm+2):
        Spart[k] = s                      # S_{k-1} = sum_{j<k}
        s += F((-1)**k, (2*k+1)**2)
    T = [F((-1)**m)*(G - Spart[m]) for m in range(maxm+1)]
    u = [T[m]/(2*m+1) for m in range(maxm+1)]
    Pi = [None]*(2*B+S+4)
    for i in range(len(Pi)):
        p = 1
        for h in range(1, B+1): p *= (2*(h+i)+1)**2
        Pi[i] = p
    def R(aa, j):
        return sum((-1)**i * comb(aa+2*B, i) * Pi[i] * u[i+j] for i in range(aa+2*B+1))
    rows = list(range(S+3))
    Rmat = {(aa, j): R(aa, j) for aa in rows for j in range(1, S+1)}

    def det(M):
        n = len(M); M = [row[:] for row in M]; d = F(1)
        for c in range(n):
            piv = next((r for r in range(c, n) if M[r][c] != 0), None)
            if piv is None: return F(0)
            if piv != c: M[c], M[piv] = M[piv], M[c]; d = -d
            d *= M[c][c]
            inv = F(1)/M[c][c]
            for r in range(c+1, n):
                f = M[r][c]*inv
                if f: M[r] = [x - f*y for x, y in zip(M[r], M[c])]
        return d

    FB = 1
    for r in range(2*B): FB *= factorial(r)
    prodPi = 1
    for i in range(N): prodPi *= Pi[i]

    print(f"B={B} S={S} q={q}  N={N}  v2(F_B)={v2(F(FB))}  2B^2={2*B*B}  v2(prod Pi)={v2(F(prodPi))}")
    for A in combinations(rows, S):
        dR = det([[Rmat[(aa, j)] for j in range(1, S+1)] for aa in A])
        if dR == 0: continue
        qhat = F(FB) * dR / prodPi
        x = F(q)**S * qhat
        HB = x.denominator                      # H_B^min
        NB = x * HB                             # the paper's nonzero integer
        assert NB.denominator == 1
        # Phase-2 probe (DIRECTION.md, node N1): the F_B-FREE integer from binomial reference
        # columns, N'_B := num(q^S det R[A,J] / prod Pi).  Its 2-adic content is gone by
        # construction; the open question is its REAL size, so we print the digit count.
        xp = F(q)**S * dR / prodPi
        NBp = xp.numerator
        print(f"  A={A}: v2(q^S detR)={v2(F(q)**S*dR):>4}  v2(H_B^min)={v2(F(HB)):>3}"
              f"  v2(N_B)={v2(NB):>5}  |N_B| ~ 2^{v2(NB)}  digits={len(str(abs(NB.numerator)))}"
              f"  |  F_B-free N'_B: v2={v2(F(NBp)) if NBp else None}  digits={len(str(abs(NBp)))}"
              f"  den(x')={len(str(xp.denominator))}d")

run(4, 2, 7, 6)
run(5, 2, 11, 10)
run(6, 3, 13, 12)
