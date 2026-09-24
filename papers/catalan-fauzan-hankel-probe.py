#!/usr/bin/env -S uv run --quiet --with python-flint --with mpmath --with sympy python3
"""Catalan twin of Fauzan's ζ(5) Hankel construction — exact probe.

Fauzan's weight comes from Hermite's formula for ζ(5,a).  The alternating Abel–Plana formula
gives the Catalan analogue.  With w(y) = π y² cosh(πy)/sinh²(πy) > 0 on (0,∞):

    ∫ y^{2e} w dy            = (-1)^e (2^{2e+2} - 1) B_{2e+2}                (rational moments)
    ∫ w/(y² + a²) dy         = a·Σ_{n≥0} (-1)^n/(n+a)² - 1/(2a)
    at a = j + 1/2:          = 2(-1)^j (2j+1)(G - T_j) - 1/(2j+1),   T_j = Σ_{m<j} (-1)^m/(2m+1)²

(both checked to 30 digits by quadrature).  So μ_X on rational functions of t = y², with poles
only at t = -(j+1/2)², is a functional whose value at X = G is integration against a positive
weight, and whose pole values are affine in X.  Work in u = 4t so poles sit at -(2j+1)².

    D_m(u) = ∏_{j<m} (u + (2j+1)²),   G_K(X)_{ik} = μ_X( D_N(u)^c u^{i+k} / D_K(u) ),  0 ≤ i,k < h = K-N

Δ_K(X) = det G_K(X) has degree h (X-part is V diag V^T with h distinct nodes), Δ_K(G) > 0.
Ledger: P_K = Δ_K / content(Δ_K) is the primitive integer polynomial; the construction proves
G ∉ ℚ iff log P_K(G) ≤ -ε K² eventually.  We print log P_K(G)/K² and its two halves.

Usage: catalan-fauzan-hankel-probe.py K N c [--quad] [--zeta5 | --zeta S]
  --zeta5 positive control: the same engine on Fauzan's ζ(5) functional.  K=40 N=3 c=6 must
          reproduce the 2026-09-22 audit (fauzan-zeta5-hankel-probe.py 1): logP/K² = -0.166.
  --quad  (h ≤ 6) known-answer control: recompute Δ_K(G) as a Gram determinant by quadrature
          against w and assert agreement with the exact polynomial evaluated at G.
"""
import sys, math
sys.set_int_max_str_digits(0)
from flint import fmpq, fmpz, fmpz_poly, fmpq_mat, fmpq_poly
from sympy import bernoulli
import mpmath as mp

K, N, c = (int(a) for a in sys.argv[1:4])
QUAD = "--quad" in sys.argv
# --zeta S: the Hermite family for ζ(S), S odd; weight w_S = 2 y^S f^{(S-1)}/(S-1)!, f = 1/(e^{2πy}-1).
#   μ(t^e) = (-1)^e B_{2e+2} (2e+S)! / ((S-1)! (2e+2)!),   μ_X(1/(t+j²)) = j^{S-1}(X - H_j^{(S)}) + 1/(2j) - 1/(S-1).
# S = 5 is exactly Fauzan's (2.2)/(2.3); --zeta5 is an alias for --zeta 5.
ZS = 5 if "--zeta5" in sys.argv else (int(sys.argv[sys.argv.index("--zeta") + 1]) if "--zeta" in sys.argv else 0)
ZETA5 = ZS > 0
h = K - N
assert c >= 1 and h >= 1
if ZETA5:
    # Fauzan: poles j in (N, K], nodes j², D_m = prod_{j=1}^{m}(t + j²); his c = 6
    poles = list(range(N + 1, K + 1))
    bnode = {j: j * j for j in poles}
    small_nodes = [j * j for j in range(1, N + 1)]
    def mu_mono_u(e):
        B = bernoulli(2 * e + 2)
        return fmpq(int(B.p), int(B.q)) * ((-1) ** e) * fmpq(math.factorial(2 * e + ZS), math.factorial(ZS - 1) * math.factorial(2 * e + 2))
    Hs = fmpq(0)
    pX, p0 = {}, {}
    for j in range(1, K + 1):
        Hs += fmpq(1, j ** ZS)
        if j in bnode:
            pX[j] = fmpq(j ** (ZS - 1))
            p0[j] = -fmpq(j ** (ZS - 1)) * Hs - fmpq(1, ZS - 1) + fmpq(1, 2 * j)
    XI = lambda: mp.zeta(ZS)
else:
    poles = list(range(N, K))
    bnode = {j: (2 * j + 1) ** 2 for j in poles}
    small_nodes = [(2 * j + 1) ** 2 for j in range(N)]
    def mu_mono_u(e):  # μ(u^e) = 4^e μ(t^e)
        B = bernoulli(2 * e + 2)
        return fmpq(int(B.p), int(B.q)) * ((-1) ** e) * (2 ** (2 * e + 2) - 1) * 4 ** e
    T = {}
    acc = fmpq(0)
    for j in range(K + 1):
        T[j] = acc
        acc += fmpq((-1) ** j, (2 * j + 1) ** 2)
    # μ_X(1/(u + (2j+1)²)) = (1/4)[2(-1)^j (2j+1)(X - T_j) - 1/(2j+1)]  =  pX_j X + p0_j
    pX = {j: fmpq(2 * (-1) ** j * (2 * j + 1), 4) for j in poles}
    p0 = {j: -pX[j] * T[j] - fmpq(1, 4 * (2 * j + 1)) for j in poles}
    XI = lambda: mp.catalan

u = fmpz_poly([0, 1])
DN = fmpz_poly([1])
for bn in small_nodes:
    DN *= (u + bn)
Wnum = DN ** (c - 1)
Dtail = fmpz_poly([1])
for j in poles:
    Dtail *= (u + bnode[j])

# residue of Wnum(u) u^m / Dtail at u = -b_j :  Wnum(-b_j)(-b_j)^m / ∏_{k≠j}(b_k - b_j)
rw = {}
for j in poles:
    den = fmpz(1)
    for k in poles:
        if k != j:
            den *= (bnode[k] - bnode[j])
    rw[j] = fmpq(Wnum(-bnode[j]), den)

maxdeg = Wnum.degree() + 2 * h
mu_cache = [mu_mono_u(e) for e in range(maxdeg + 1)]
a, b = [], []
for m in range(2 * h - 1):
    Qp, _ = divmod(Wnum * u ** m, Dtail)
    am = sum((fmpq(cf) * mu_cache[e] for e, cf in enumerate(Qp.coeffs()) if cf != 0), fmpq(0))
    bm = fmpq(0)
    for j in poles:
        cj = rw[j] * fmpq(-bnode[j]) ** m
        am += cj * p0[j]
        bm += cj * pX[j]
    a.append(am); b.append(bm)

A = fmpq_mat(h, h, [a[i + k] for i in range(h) for k in range(h)])
B = fmpq_mat(h, h, [b[i + k] for i in range(h) for k in range(h)])
# Δ(X) = det(A + X B) = det(B) · det(X I + B⁻¹A) = det(B) · charpoly(-B⁻¹A)(X)
C = -(B.inv() * A)
cp = C.charpoly()
Delta = cp * B.det()
cs = Delta.coeffs()
assert len(cs) - 1 == h

# content = gcd(numerators) / lcm(denominators)
num_g = fmpz(0); den_l = fmpz(1)
for q in cs:
    if q != 0:
        num_g = fmpz(math.gcd(int(num_g), int(q.p)))
        den_l = den_l * q.q // math.gcd(int(den_l), int(q.q))
digits = max(len(str(abs(int(q.p)))) + len(str(int(q.q))) for q in cs)

def horner(dps):
    mp.mp.dps = dps
    g = XI()
    s = mp.mpf(0)
    for q in reversed(cs):
        s = s * g + mp.mpf(int(q.p)) / mp.mpf(int(q.q))
    return s
v1 = horner(digits + 100); v2 = horner(digits + 300)
assert v2 > 0, "Δ_K(G) must be positive"
assert abs(v1 - v2) < abs(v2) * mp.mpf(10) ** (-30), "evaluation unstable"
logD = mp.log(v2)
logcont = mp.log(int(num_g)) - mp.log(int(den_l))
logP = logD - logcont
K2 = K * K
print(f"{('zeta'+str(ZS)) if ZS else 'catalan'} K={K} N={N} c={c} h={h}  logΔ(G)/K²={mp.nstr(logD / K2, 6)}  "
      f"-log content/K²={mp.nstr(-logcont / K2, 6)}  logP(G)/K²={mp.nstr(logP / K2, 6)}  "
      f"logP(G)/h²={mp.nstr(logP / (h * h), 6)}")

if QUAD:
    assert h <= 6
    mp.mp.dps = 40
    wt = lambda y: mp.pi * y**2 * mp.cosh(mp.pi * y) / mp.sinh(mp.pi * y)**2
    def R(y, m):
        uu = 4 * y * y
        dn = mp.fprod(uu + (2 * j + 1)**2 for j in range(N))
        dk = mp.fprod(uu + (2 * j + 1)**2 for j in range(K))
        return dn**c * uu**m / dk
    mom = [mp.quad(lambda y: R(y, m) * wt(y), [0, 1, 4, 16, mp.inf]) for m in range(2 * h - 1)]
    Gq = mp.det(mp.matrix([[mom[i + k] for k in range(h)] for i in range(h)]))
    rel = abs(Gq - v2) / v2
    print(f"--quad control: quadrature det = {mp.nstr(Gq, 15)}  exact Δ(G) = {mp.nstr(v2, 15)}  rel err {mp.nstr(rel, 3)}")
    assert rel < mp.mpf(10)**-15, "CONTROL FAILED"
