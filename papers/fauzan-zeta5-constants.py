#!/usr/bin/env -S uv run --quiet --with mpmath --with sympy python3
"""Numerical checks of the constants in Fauzan 2026, "ζ(5) is irrational" (Zenodo 22826419).

  Lemma 6.1  the sixteen-arcsine measure ρ of Table 1: max_t (2U^ρ(t) - V(t)) vs M0 = -1329/200,
             I(ρ), C* (6.3), and U = λM0 - I(ρ) + C*  (paper: -2733991/2000000)
  (5.18)     ∫_3^20 R(x)/x^3 dx from the explicit (5.12)-(5.13)+(B.1), and from (5.4)-(5.6) directly
  (5.16)     ∫_20^∞ R/x^3 ≤ -2689/48000
  (5.10)     I_out = ∫_{1/3}^{2λ} T(y) dy = 127751/96000, and (4.14) vs (5.8) at a large K
  (7.2)      A_200 + U, times -1600, vs 139/5
"""
import math, sys
import mpmath as mp
from sympy import primerange

mp.mp.dps = 30
alpha = mp.mpf(3) / 40; lam = mp.mpf(37) / 40; H = 1 + 2 * alpha

# ---------------- Lemma 6.1 ----------------
tbl = [
    (3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
    (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
    (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
    (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
    (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
    (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
    (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
    (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577),
]
E = mp.mpf(10) ** 12
rho = [(mp.mpf(a) / E, mp.mpf(b) / E, mp.mpf(c) / E) for a, b, c in tbl]
print("Σc_j =", sum(c for _, _, c in rho), " (should be 37/40 =", lam, ")")
nested = all(rho[j][0] < rho[j - 1][0] and rho[j][1] > rho[j - 1][1] for j in range(1, 16))
print("nested:", nested, " min length:", min(b - a for a, b, _ in rho), "> 1/225 =", mp.mpf(1) / 225)

def U_arcsine(t, a, b):
    if a <= t <= b:
        return mp.log((b - a) / 4)
    m = (a + b) / 2
    return mp.log((abs(t - m) + mp.sqrt((t - a) * (t - b))) / 2)

def Urho(t):
    return sum(c * U_arcsine(t, a, b) for a, b, c in rho)

def V(t):  # (A.5)
    if t == 0:
        return -12 * alpha * mp.log(alpha) - 2 + 12 * alpha
    s = mp.sqrt(t)
    return (mp.log(1 + t) - 6 * alpha * mp.log(t + alpha ** 2) - 2 + 12 * alpha
            + 2 * s * (mp.pi + mp.atan(1 / s) - 6 * mp.atan(alpha / s)))

def g(t):
    return 2 * Urho(t) - V(t)

# scan [0, 6] finely, then refine around the top few
grid = [mp.mpf(i) / 20000 for i in range(0, 120001)]
vals = [(g(t), t) for t in grid]
vals.sort(reverse=True)
best = vals[0]
for _, t0 in vals[:5]:
    lo, hi = max(t0 - mp.mpf(1) / 20000, 0), t0 + mp.mpf(1) / 20000
    for _ in range(60):
        m1 = lo + (hi - lo) / 3; m2 = hi - (hi - lo) / 3
        if g(m1) < g(m2): lo = m1
        else: hi = m2
    cand = (g((lo + hi) / 2), (lo + hi) / 2)
    if cand > best: best = cand
M0 = mp.mpf(-1329) / 200
print(f"max_t (2U^ρ - V) ≈ {mp.nstr(best[0], 12)} at t ≈ {mp.nstr(best[1], 8)};  paper M0 = {mp.nstr(M0, 8)};  bound holds: {best[0] <= M0}")
print(f"tail check g(2)={mp.nstr(g(2),8)}  g(10)={mp.nstr(g(10),8)}  g(100)={mp.nstr(g(100),8)}")

S = mp.mpf(0); Irho = mp.mpf(0)
for a, b, c in rho:
    Snew = S + c
    Irho += (Snew ** 2 - S ** 2) * mp.log((b - a) / 4)
    S = Snew
Cstar = -2 * lam + 12 * alpha * lam * (1 - mp.log(alpha)) + 3 * lam ** 2 - 2 * lam ** 2 * mp.log(2 * lam)
U = lam * M0 - Irho + Cstar
print(f"I(ρ) = {mp.nstr(Irho, 12)}  (paper: -2.126593445148)   C* = {mp.nstr(Cstar, 12)} (paper: 2.653035990340)")
print(f"U = λM0 - I(ρ) + C* = {mp.nstr(U, 12)}   (paper: -2733991/2000000 = {mp.nstr(mp.mpf(-2733991)/2000000, 12)})")
# what the SAME bound gives with the best-possible M0 for this ρ
print(f"with M0 := measured sup, U would be {mp.nstr(lam * best[0] - Irho + Cstar, 12)}")

# ---------------- inner integrand R(x) ----------------
def frac(x): return x - mp.floor(x)
def d0(u): return min(u, 1 - u)
def e(u): return 1 if u <= mp.mpf(1) / 2 else -1

def R_explicit(x):  # (5.12), (5.13), (B.1)
    f, gg = frac(x), frac(alpha * x)
    tau, sig, eta = frac(2 * H * x), frac(2 * x), frac(2 * lam * x)
    F = 4 * lam + 2 * lam * f - 12 * lam * gg
    B2 = d0(gg) * (1 - 2 * d0(gg))
    AB = e(f) * e(gg) * (min(d0(f), d0(gg)) - 2 * d0(f) * d0(gg))
    Q = (tau * (tau - sig) - max(tau - sig, 0) + eta * (1 - eta)) / 2 + 9 * B2 - 3 * AB
    return x * F + Q

def ell(x, z): return mp.floor(x - z) + mp.floor(x + z) + 1
def R_direct(x):  # (5.4)-(5.6)
    T = mp.floor(2 * H * x); s = H * x - T / 2; q = mp.floor(2 * x); nplus = (2 * x - q) / 2
    # integrand piecewise constant in z; integrate exactly over breakpoints
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
    G += s * (2 * T - q - 5) + max(s - nplus, 0)
    m = mp.floor(2 * lam * x); J = m * lam * x - m * (m + 1) / 4
    Nx = 2 * lam * x * mp.floor(x) - 12 * lam * x * mp.floor(alpha * x) - 2 * J
    return -G - Nx

xs = [3 + mp.mpf(i) * 17 / 100000 for i in range(100001)]
maxdiff = max(abs(R_explicit(x) - R_direct(x)) for x in xs[::50])
print(f"\nmax |R_explicit - R_direct| on [3,20] (sampled): {mp.nstr(maxdiff, 6)}")
I_inner = sum(R_explicit((x1 + x2) / 2) / ((x1 + x2) / 2) ** 3 * (x2 - x1) for x1, x2 in zip(xs, xs[1:]))
paper_inner = mp.mpf(322437603634266857629) / 7535670527041937280000
print(f"∫_3^20 R/x^3 ≈ {mp.nstr(I_inner, 10)}   paper (5.18) = {mp.nstr(paper_inner, 10)}")
xs2 = [20 + mp.mpf(i) * 1980 / 400000 for i in range(400001)]
I_tail = sum(R_explicit((x1 + x2) / 2) / ((x1 + x2) / 2) ** 3 * (x2 - x1) for x1, x2 in zip(xs2, xs2[1:]))
print(f"∫_20^2000 R/x^3 ≈ {mp.nstr(I_tail, 8)}   paper (5.16) bound ∫_20^∞ ≤ -2689/48000 = {mp.nstr(mp.mpf(-2689)/48000, 8)}")

# ---------------- outer integrand ----------------
def R0(y):
    if y < mp.mpf(1) / 3 or y > 1: return mp.mpf(0)
    if y < mp.mpf(1) / 2:
        return 8 - 9 * y - 8 * alpha - 5 * min(alpha, 1 - 2 * y) - 5 * max(1 + alpha - 3 * y, 0)
    return 7 * (1 - y) - 6 * min(alpha, 1 - y) - 6 * max(1 + alpha - 2 * y, 0) + max(1 + 4 * alpha - 2 * y, 0)
def dfun(y):
    if mp.mpf(1) / 3 < y < mp.mpf(1) / 2:
        return max(1 + 4 * alpha - 3 * y - max(1 + alpha - 3 * y, 0), 0)
    return mp.mpf(0)
def Tout(y):
    return R0(y) - dfun(y) - 2 * lam * mp.floor(1 / y) + sum(max(2 * lam - j * y, 0) for j in range(1, 6))
ys = [mp.mpf(1) / 3 + (2 * lam - mp.mpf(1) / 3) * i / 400000 for i in range(400001)]
I_out = sum(Tout((y1 + y2) / 2) * (y2 - y1) for y1, y2 in zip(ys, ys[1:]))
print(f"\nI_out ≈ {mp.nstr(I_out, 10)}   paper (5.10) = 127751/96000 = {mp.nstr(mp.mpf(127751)/96000, 10)}")

# (4.14) vs (5.8): -γ_p^out/K vs R0(p/K) - d(p/K), and the full outer prime sum vs I_out
def legendre(m, p):
    s, q = 0, p
    while q <= m:
        s += m // q; q *= p
    return s
Kbig = 40 * 3000
Nb, hb = 3 * 3000, 37 * 3000
def gamma_out(p, K, N):
    v = K - p * (K // p); u = max(0, N + v - p + 1); tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)
def vpS(p, K, N, h):
    v = 2 * h * legendre(K, p) - 12 * h * legendre(N, p) - 2 * sum(legendre(2 * i, p) for i in range(1, h))
    if p == 2: v += 2 * (h - 1)
    return v
worst = 0; total = mp.mpf(0)
for p in primerange(Kbig // 3 + 1, 2 * hb + 1):
    y = mp.mpf(p) / Kbig
    g_ = gamma_out(p, Kbig, Nb) if p <= Kbig else 0
    pred = Kbig * (R0(y) - dfun(y))
    worst = max(worst, abs(-g_ - pred))
    total += -(vpS(p, Kbig, Nb, hb) + g_) * mp.log(p)
print(f"K={Kbig}: max |(-γ_p^out) - K(R0-d)(p/K)| over outer primes = {worst}  (paper: O(1))")
print(f"K={Kbig}: Σ_{{K/3<p≤2h}} -L_p log p / K^2 = {mp.nstr(total / Kbig ** 2, 8)}   vs I_out {mp.nstr(mp.mpf(127751)/96000, 8)}")

# ---------------- (7.2) ----------------
Astar = mp.mpf(9928298118277006344769) / 7535670527041937280000
def A_M(M): return Astar + 7 * lam / M - (mp.mpf(2923) / 240 - mp.mpf(1) / 4) / M ** 2 + 32 / mp.mpf(M) ** 3
Upaper = mp.mpf(-2733991) / 2000000
print(f"\nA_200 = {mp.nstr(A_M(200), 10)}  U = {mp.nstr(Upaper, 10)}  A_200+U = {mp.nstr(A_M(200)+Upaper, 8)}  -1600(A_200+U) = {mp.nstr(-1600*(A_M(200)+Upaper), 8)} vs 139/5 = 27.8")
print(f"margin as a fraction of the arithmetic side: {mp.nstr(-(A_M(200)+Upaper)/A_M(200), 6)}")
