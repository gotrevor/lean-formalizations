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

import sys as _sys
if len(_sys.argv) == 1:
    run(4, 2, 7, 6)
    run(5, 2, 11, 10)
    run(6, 3, 13, 12)

# ---------------------------------------------------------------------------
# Growth probe (2026-09-04, architect): does the F_B-free integer N'_B SHRINK
# or GROW in B?  For each B print, minimised over admissible row sets A,
#   log10|x'| = log10|q^S det R[A,J] / prod Pi|   (real size before integerizing)
#   log10 den(x')                                  (the minimal integerizer)
#   log10|N'_B| = sum of the two                   (must go to -inf for a proof)
# A slope that is positive in B (or a positive B^2 coefficient) refutes N1.
import sys
from math import log10

def growth(B, S, q, a):
    G = F(a, q); N = 2*B + S + 3
    maxm = (2*B + S + 2) + S + 2
    Spart = [F(0)]*(maxm+2); s = F(0)
    for k in range(maxm+2):
        Spart[k] = s; s += F((-1)**k, (2*k+1)**2)
    T = [F((-1)**m)*(G - Spart[m]) for m in range(maxm+1)]
    u = [T[m]/(2*m+1) for m in range(maxm+1)]
    Pi = []
    for i in range(2*B+S+4):
        p = 1
        for h in range(1, B+1): p *= (2*(h+i)+1)**2
        Pi.append(p)
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
            d *= M[c][c]; inv = F(1)/M[c][c]
            for r in range(c+1, n):
                f = M[r][c]*inv
                if f: M[r] = [x - f*y for x, y in zip(M[r], M[c])]
        return d
    prodPi = 1
    for i in range(N): prodPi *= Pi[i]
    best = None
    for A in combinations(rows, S):
        dR = det([[Rmat[(aa, j)] for j in range(1, S+1)] for aa in A])
        if dR == 0: continue
        xp = F(q)**S * dR / prodPi
        lx = log10(abs(xp.numerator)) - log10(xp.denominator)
        ld = log10(xp.denominator)
        ln = log10(abs(xp.numerator))
        # also the raw minor size, before the normaliser
        lr = log10(abs(dR.numerator)) - log10(dR.denominator)
        if best is None or ln < best[2]:
            best = (lx, ld, ln, lr, A)
    lx, ld, ln, lr, A = best
    print(f"B={B:>2} S={S} q={q} N={N:>2} | log10|detR|={lr:8.2f} log10|x'|={lx:8.2f} "
          f"log10 den={ld:7.2f} => log10|N'_B|={ln:7.2f}  (A={A})  B^2={B*B}")

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "growth":
    Bmax = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    q, a = 7, 6
    for B in range(max(S+1, 3), Bmax+1):
        growth(B, S, q, a)

# ---------------------------------------------------------------------------
# Ledger probe (2026-09-04, architect).  The fake-rational probes above are the
# wrong instrument for the real place: with G = a/q the "tails" do not decay.
# Here G is a FORMAL variable.  det R[A,J] is a polynomial P_A(G) of degree <= S
# with rational coefficients (R is linear in G); interpolate it exactly from
# S+1 rational evaluation points.  Then, with y_A(G) := P_A(G)/prod_{i<N} Pi_i:
#   Delta_B := lcm of the coefficient denominators of y_A   (uniform integerizer:
#              for ANY a/q, Delta_B * q^S * y_A(a/q) is an integer)
#   |y_A(G_true)| at 4000 digits                             (real-place size)
# The proof needs  log Delta_B + S log q + log|y_A(G_true)|  ->  -infinity.
# The sign of its slope in B is the verdict on the CONSTRUCTION (independent of
# F_B, i.e. this already includes the N1 binomial completion).
from math import lcm, log

def _interp(xs, ys):
    """Lagrange interpolation over Fractions; returns coefficient list, low first."""
    n = len(xs); coeffs = [F(0)]*n
    for i in range(n):
        # basis polynomial l_i
        num = [F(1)]; den = F(1)
        for j in range(n):
            if j == i: continue
            num = [F(0)] + num
            for k in range(len(num)-1):
                num[k] -= xs[j]*num[k+1]
            den *= (xs[i]-xs[j])
        for k in range(n):
            coeffs[k] += ys[i]*num[k]/den
    return coeffs

def ledger(B, S, dps=4000):
    import mpmath
    mpmath.mp.dps = dps
    N = 2*B + S + 3
    maxm = (2*B + S + 2) + S + 2
    Spart = [F(0)]*(maxm+2); s = F(0)
    for k in range(maxm+2):
        Spart[k] = s; s += F((-1)**k, (2*k+1)**2)
    Pi = []
    for i in range(2*B+S+4):
        p = 1
        for h in range(1, B+1): p *= (2*(h+i)+1)**2
        Pi.append(p)
    prodPi = 1
    for i in range(N): prodPi *= Pi[i]
    rows = list(range(S+3))
    def det(M):
        n = len(M); M = [row[:] for row in M]; d = F(1)
        for c in range(n):
            piv = next((r for r in range(c, n) if M[r][c] != 0), None)
            if piv is None: return F(0)
            if piv != c: M[c], M[piv] = M[piv], M[c]; d = -d
            d *= M[c][c]; inv = F(1)/M[c][c]
            for r in range(c+1, n):
                f = M[r][c]*inv
                if f: M[r] = [x - f*y for x, y in zip(M[r], M[c])]
        return d
    def Rmat_at(Gval):
        T = [F((-1)**m)*(Gval - Spart[m]) for m in range(maxm+1)]
        u = [T[m]/(2*m+1) for m in range(maxm+1)]
        return {(aa, j): sum((-1)**i * comb(aa+2*B, i) * Pi[i] * u[i+j]
                             for i in range(aa+2*B+1)) for aa in rows for j in range(1, S+1)}
    xs = [F(t) for t in range(S+1)]
    mats = [Rmat_at(x) for x in xs]
    Gtrue = mpmath.catalan
    best = None
    for A in combinations(rows, S):
        ys = [det([[M[(aa, j)] for j in range(1, S+1)] for aa in A]) for M in mats]
        P = _interp(xs, ys)
        if all(c == 0 for c in P): continue
        y = [c/prodPi for c in P]
        Delta = 1
        for c in y: Delta = lcm(Delta, c.denominator)
        val = mpmath.mpf(0)
        for k, c in enumerate(y):
            val += mpmath.mpf(c.numerator)/mpmath.mpf(c.denominator) * Gtrue**k
        if val == 0: continue
        lreal = float(mpmath.log10(abs(val)))
        lden = log10(Delta)
        tot = lreal + lden
        if best is None or tot < best[0]:
            best = (tot, lreal, lden, A, Delta)
    tot, lreal, lden, A, Delta = best
    v2D = 0; d = Delta
    while d % 2 == 0: d //= 2; v2D += 1
    print(f"B={B:>2} S={S} N={N:>2} | log10|y(G)|={lreal:9.2f}  log10 Delta={lden:8.2f}  v2(Delta)={v2D:>4}"
          f"  => log10|N| (q=1)={tot:8.2f}   B^2={B*B}  A={A}")

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "ledger":
    Bmax = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    for B in range(max(S+1, 3), Bmax+1):
        ledger(B, S)
