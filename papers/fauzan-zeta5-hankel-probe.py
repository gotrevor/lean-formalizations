#!/usr/bin/env -S uv run --quiet --with python-flint --with mpmath --with sympy python3
"""Exact probe of Fauzan 2026, "ζ(5) is irrational" (Zenodo 22826419), §2-§5.

Builds the Hankel matrix G_K(X) of (2.4) exactly for K = 40n (N = 3n, h = 37n), computes
Δ_K(X) = det G_K(X) ∈ Q[X] by evaluation at h+1 integer points + Newton interpolation, and
checks the paper's own local claims where their hypotheses are satisfied at this K:

  (2.9)   leading coefficient  [X^h]Δ_K = (-1)^{h(h-1)/2} ∏_{j=N+1}^{K} j^4 D_N(-j^2)^5
  §2.4    Δ_K(ζ(5)) > 0
  (3.12)  v_p^G(F_K) ≥ -6h⌊log_p(5K)⌋ - h·v_p(24)   for EVERY prime p   (F_K = S_K Δ_K)
  Prop 4.3 v_p^G(Δ_K) ≥ γ_p^out of (4.14) for primes with (4.9), and v_p^G(Δ_K) ≥ 0 for p > K

and prints the exact content of Δ_K and the primitive-polynomial ledger log P_K(ζ(5)).

Usage: fauzan-zeta5-hankel-probe.py [n]      (n=1 → K=40, h=37; n=2 → K=80, h=74; ...)
"""
import sys, math
sys.set_int_max_str_digits(0)
from flint import fmpq, fmpz, fmpz_mat, fmpz_poly, fmpq_poly
from sympy import bernoulli, primerange
import mpmath as mp

n = int(sys.argv[1]) if len(sys.argv) > 1 else 1
K, N, h = 40 * n, 3 * n, 37 * n
poles = list(range(N + 1, K + 1))          # K - N = h poles
assert len(poles) == h

def vp_int(m, p):
    v = 0
    m = abs(int(m))
    if m == 0:
        return None
    while m % p == 0:
        m //= p; v += 1
    return v

def vp(q, p):
    if q == 0:
        return None
    return vp_int(q.p, p) - vp_int(q.q, p)

def legendre(m, p):
    s, q = 0, p
    while q <= m:
        s += m // q; q *= p
    return s

# ---- the functional (2.2), (2.3) -------------------------------------------------------
def mu_mono(e):  # μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24
    B = bernoulli(2 * e + 2)
    return fmpq(int(B.p), int(B.q)) * ((-1) ** e) * (2 * e + 3) * (2 * e + 4) * (2 * e + 5) / 24

H5 = {}
acc = fmpq(0)
for j in range(1, K + 1):
    acc += fmpq(1, j ** 5)
    H5[j] = acc

# ---- partial fractions of D_N(t)^5 t^m / D_tail(t) -----------------------------------
t = fmpz_poly([0, 1])
DN = fmpz_poly([1])
for j in range(1, N + 1):
    DN *= (t + j * j)
DN5 = DN ** 5
Dtail = fmpz_poly([1])
for j in poles:
    Dtail *= (t + j * j)

# residue weights w_j = D_N(-j^2)^5 / ∏_{k≠j}(k^2 - j^2)
w = {}
for j in poles:
    num = fmpz(1)
    for i in range(1, N + 1):
        num *= (i * i - j * j)
    num = num ** 5
    den = fmpz(1)
    for k in poles:
        if k != j:
            den *= (k * k - j * j)
    w[j] = fmpq(num, den)

pole_const = {j: -fmpq(j ** 4) * H5[j] - fmpq(1, 4) + fmpq(1, 2 * j) for j in poles}

a = []; b = []
maxdeg = 5 * N + 2 * h - 2
mu_cache = [mu_mono(e) for e in range(maxdeg + 1)]
for m in range(2 * h - 1):
    R = DN5 * (t ** m)
    Qp, rem = divmod(R, Dtail)
    am = fmpq(0); bm = fmpq(0)
    for e, c in enumerate(Qp.coeffs()):
        if c != 0:
            am += fmpq(c) * mu_cache[e]
    for j in poles:
        cj = w[j] * (fmpq(-j * j) ** m)
        am += cj * pole_const[j]
        bm += cj * (j ** 4)
    a.append(am); b.append(bm)

# ---- determinant Δ_K(X) by evaluation + interpolation --------------------------------
D = fmpz(1)
for q in a + b:
    D = D * q.q // math.gcd(int(D), int(q.q))
A = [fmpz(q.p) * (D // q.q) for q in a]
B = [fmpz(q.p) * (D // q.q) for q in b]

xs = list(range(h + 1))
ys = []
for x in xs:
    M = fmpz_mat(h, h, [A[i + j] + B[i + j] * x for i in range(h) for j in range(h)])
    ys.append(fmpq(M.det(), D ** h))

# Newton divided differences
dd = list(ys)
coef = [dd[0]]
for k in range(1, h + 1):
    dd = [(dd[i + 1] - dd[i]) / (xs[i + k] - xs[i]) for i in range(len(dd) - 1)]
    coef.append(dd[0])
X = fmpq_poly([0, 1])
Delta = fmpq_poly([0])
basis = fmpq_poly([1])
for k, c in enumerate(coef):
    Delta += basis * c
    basis *= (X - xs[k])
cs = Delta.coeffs()
deg = len(cs) - 1
print(f"K={K} N={N} h={h}   deg Δ_K = {deg}")

# (2.9)
lead = fmpz(1)
for j in poles:
    dn = fmpz(1)
    for i in range(1, N + 1):
        dn *= (i * i - j * j)
    lead *= fmpz(j ** 4) * dn ** 5
lead = lead * ((-1) ** ((h * (h - 1) // 2) % 2))
print(f"(2.9) leading coefficient matches: {deg == h and cs[h] == fmpq(lead)}")

# ---- p-adic table --------------------------------------------------------------------
def vpS(p):  # v_p(S_K), S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)^2)
    v = 2 * h * legendre(K, p) - 12 * h * legendre(N, p) - 2 * sum(legendre(2 * i, p) for i in range(1, h))
    if p == 2:
        v += 2 * (h - 1)
    return v

def gamma_out(p):  # (4.14)
    v = K - p * (K // p)
    u = max(0, N + v - p + 1)
    tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)

alpha_ = 3 / 40; lam_ = 37 / 40; H_ = 1 + 2 * alpha_
def ell_(x, z): return math.floor(x - z) + math.floor(x + z) + 1
def Gamma_(x):  # (5.4), piecewise-constant integrand integrated exactly over its breakpoints
    T = math.floor(2 * H_ * x); s_ = H_ * x - T / 2; q = math.floor(2 * x); nplus = (2 * x - q) / 2
    bps = {0.0, 0.5}
    for y in (x, alpha_ * x):
        for k in range(math.floor(y) - 1, math.floor(y) + 3):
            for z in (y - k, k - y):
                if 0 < z < 0.5: bps.add(z)
    bps = sorted(bps); G = 0.0
    for lo, hi in zip(bps, bps[1:]):
        z = (lo + hi) / 2; bz = 3 * ell_(alpha_ * x, z); lz = ell_(x, z)
        G += (T - bz) * (T + bz - lz - 5) * (hi - lo)
    return G + s_ * (2 * T - q - 5) + max(s_ - nplus, 0)

def cond49(p):
    return p >= 7 and p <= K < 3 * p and p * p > 2 * K and 2 * N < p and 5 * N <= 2 * p - 2

print(f"\n{'p':>5} {'vG(Δ)':>7} {'(3.12)':>8} {'γ_out':>7} {'pΓ(K/p)':>9} {'vG(F)':>7} {'note'}")
costF = {"p<=K/3": 0.0, "K/3<p<=K": 0.0, "p>K": 0.0}
viol = []
logden = 0.0; lognum = 0.0
by_range = {"p<=K/3": 0.0, "K/3<p<=K": 0.0, "p>K": 0.0}
residual_den = fmpz(1)
for c in cs:
    residual_den = residual_den * c.q // math.gcd(int(residual_den), int(c.q))
for p in primerange(2, 2 * K + 1):
    vals = [vp(c, p) for c in cs if c != 0]
    vG = min(vals)
    b312 = -6 * h * int(math.floor(math.log(5 * K) / math.log(p) + 1e-12)) - h * vp_int(24, p) - vpS(p)
    note = ""
    if vG < b312:
        note += " VIOLATES (3.12)"
    gout = ""; gin = ""
    if 3 * p <= K:
        gin = f"{p * Gamma_(K / p):.1f}" + ("*" if p * p > 5 * K else "")
    vF = vG + vpS(p)
    rngF = "p<=K/3" if 3 * p <= K else ("K/3<p<=K" if p <= K else "p>K")
    if vF < 0:
        costF[rngF] += -vF * math.log(p)
    if cond49(p):
        g = gamma_out(p); gout = str(g)
        if vG < g:
            note += " VIOLATES Prop4.3"
    elif p > K:
        gout = "0"
        if vG < 0:
            note += " VIOLATES p>K integrality"
    if note:
        viol.append((p, vG, note))
    if vG < 0:
        logden += -vG * math.log(p)
        rng = "p<=K/3" if 3 * p <= K else ("K/3<p<=K" if p <= K else "p>K")
        by_range[rng] += -vG * math.log(p)
    else:
        lognum += vG * math.log(p)
    while residual_den % p == 0:
        residual_den //= p
    print(f"{p:>5} {vG:>7} {b312:>8} {gout:>7} {gin:>9} {vF:>7}{note}")
print(f"residual denominator after primes ≤ 2K: {residual_den}")
print("(* = p^2 > 5K, the window where Prop 4.1's inner-range hypotheses on p hold; K ≥ 200M^2 never does)")
print(f"F_K denominator cost by range, / K^2:  " + "  ".join(f"{k}: {v / (K * K):.4f}" for k, v in costF.items()) + "   (paper limits: inner ≈ -0.017+6λ/M, outer 1.3307)")
print(f"\nVIOLATIONS: {viol if viol else 'none'}")

# ---- real side -------------------------------------------------------------------------
digits = max(len(str(abs(int(c.p)))) + len(str(int(c.q))) for c in cs)
mp.mp.dps = digits + 200
xi = mp.zeta(5)
def horner(dps):
    mp.mp.dps = dps
    z = mp.zeta(5)
    acc = mp.mpf(0)
    for c in reversed(cs):
        acc = acc * z + mp.mpf(int(c.p)) / mp.mpf(int(c.q))
    return acc
v1 = horner(digits + 200); v2 = horner(digits + 400)
assert abs(v1 - v2) < abs(v2) * mp.mpf(10) ** (-50), "evaluation unstable"
val = v2
logS = 2 * h * mp.loggamma(K + 1) + (h - 1) * mp.log(4) - 12 * h * mp.loggamma(N + 1) - 2 * sum(mp.loggamma(2 * i + 1) for i in range(1, h))
print(f"\nΔ_K(ζ(5)) > 0: {val > 0}     log Δ_K(ζ(5)) = {mp.nstr(mp.log(val), 12)}")
print(f"log S_K = {mp.nstr(logS, 12)}   log F_K(ζ(5)) = {mp.nstr(mp.log(val) + logS, 12)}   paper (6.16) bound U K^2+24K logK+200K = {mp.nstr(-1.3669955 * K * K + 24 * K * mp.log(K) + 200 * K, 12)}")
print(f"log(denominator clearing of Δ_K) = {logden:.4f}  by range {by_range}")
print(f"log(numerator content of Δ_K)   = {lognum:.4f}")
logP = mp.log(val) - lognum + logden
print(f"primitive P_K(ζ(5)): log = {mp.nstr(logP, 12)}   /K^2 = {mp.nstr(logP / (K * K), 8)}")
print(f"log F_K(ζ(5))/K^2 = {mp.nstr((mp.log(val) + logS) / (K * K), 8)}  (paper limit ≤ U = -1.367);  -log cont(F_K)/K^2 = {mp.nstr((logP - mp.log(val) - logS) / (K * K), 8)}  (paper limit ≤ A_200 = 1.3496)")
