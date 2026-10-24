#!/usr/bin/env -S uv run --quiet --with python-flint --with mpmath --with sympy python3
"""Fauzan/Hermite Hankel family for zeta(S) with a choice of pole lattice (u = 4t, nodes n^2).

Hermite weight w_S = 2 y^S f^{(S-1)}/(S-1)!, f = 1/(e^{2 pi y}-1).  For any a > 0:
    mu_X(1/(t + a^2)) = a^{S-1} zeta(S, a) - 1/(2a) - 1/(S-1)            (checked by --quad)
zeta(S, j)     = X - H_{j-1}^{(S)}                       (a = n/2, n = 2j even)
zeta(S, j+1/2) = (2^S - 1) X - 2^S O_j,  O_j = sum_{m<j} (2m+1)^{-S}   (n = 2j+1 odd)
Both are affine in X = zeta(S): the beam stays narrow.

Pole sets (u-nodes n^2):  int  : n = 2j, j in (N, K]          (= Fauzan; control vs catalan-fauzan-hankel-probe --zeta S)
                          half : n = 2j+1, j in [N, K)
                          dense: n in (2N, 2K]  (all half-integers a = n/2)
Field D_N^{c-1} over the matching small nodes.  Ledger log P_K(zeta(S))/K^2 as in the original probe.
Usage: hermite-pole-lattice-probe.py K N c S {int|half|dense} [--ranges] [--quad]
"""
import sys, math
sys.set_int_max_str_digits(0)
from flint import fmpq, fmpz, fmpz_poly, fmpq_mat
from sympy import bernoulli, primerange
import mpmath as mp

K, N, c, S = (int(a) for a in sys.argv[1:5]); MODE = sys.argv[5]
if MODE == "int":
    big = [2*j for j in range(N+1, K+1)]; small = [2*j for j in range(1, N+1)]
elif MODE == "half":
    big = [2*j+1 for j in range(N, K)]; small = [2*j+1 for j in range(N)]
elif MODE == "dense":
    big = list(range(2*N+1, 2*K+1)); small = list(range(1, 2*N+1))
else: raise SystemExit("mode")
h = len(big)

def mu_mono_u(e):  # mu(u^e) = 4^e mu(t^e),  mu(t^e) = (-1)^e B_{2e+2} (2e+S)! / ((S-1)! (2e+2)!)
    B = bernoulli(2*e+2)
    return fmpq(int(B.p), int(B.q)) * ((-1)**e) * fmpq(math.factorial(2*e+S), math.factorial(S-1)*math.factorial(2*e+2)) * 4**e

H = [fmpq(0)]                      # H[j] = sum_{m<=j} m^-S
for m in range(1, K+2): H.append(H[-1] + fmpq(1, m**S))
O = [fmpq(0)]                      # O[j] = sum_{m<j} (2m+1)^-S
for m in range(0, K+2): O.append(O[-1] + fmpq(1, (2*m+1)**S))
pX, p0 = {}, {}
for n in big:                       # mu_X(1/(u+n^2)) = (1/4) mu_X(1/(t+(n/2)^2))
    a = fmpq(n, 2); aS = a**(S-1)
    if n % 2 == 0:
        j = n//2; zx, z0 = fmpq(1), -H[j-1]
    else:
        j = (n-1)//2; zx, z0 = fmpq(2**S - 1), -fmpq(2**S)*O[j]
    pX[n] = aS*zx/4
    p0[n] = (aS*z0 - 1/(2*a) - fmpq(1, S-1))/4

u = fmpz_poly([0, 1]); DN = fmpz_poly([1])
TAPER = "--taper" in sys.argv
if TAPER:   # multiplicity of node n: round((c-1)*(1 - (i)/len(small))) , linearly decreasing
    W = fmpz_poly([1])
    for i, n in enumerate(small): W *= (u + n*n)**max(0, round((c-1)*(1 - i/len(small))))
else:
    for n in small: DN *= (u + n*n)
    W = DN**(c-1); Dt = fmpz_poly([1])
Dt = fmpz_poly([1])
for n in big: Dt *= (u + n*n)
rw = {}
for n in big:
    den = fmpz(1)
    for k in big:
        if k != n: den *= (k*k - n*n)
    rw[n] = fmpq(W(-n*n), den)
mu_cache = [mu_mono_u(e) for e in range(W.degree() + 2*h + 1)]
a_, b_ = [], []
for m in range(2*h-1):
    Qp, _ = divmod(W*u**m, Dt)
    am = sum((fmpq(cf)*mu_cache[e] for e, cf in enumerate(Qp.coeffs()) if cf != 0), fmpq(0)); bm = fmpq(0)
    for n in big:
        cj = rw[n]*fmpq(-n*n)**m; am += cj*p0[n]; bm += cj*pX[n]
    a_.append(am); b_.append(bm)
A = fmpq_mat(h, h, [a_[i+k] for i in range(h) for k in range(h)])
B = fmpq_mat(h, h, [b_[i+k] for i in range(h) for k in range(h)])
cs = ((-(B.inv()*A)).charpoly()*B.det()).coeffs()
num_g = fmpz(0); den_l = fmpz(1)
for q in cs:
    if q != 0:
        num_g = fmpz(math.gcd(int(num_g), int(q.p))); den_l = den_l*q.q//math.gcd(int(den_l), int(q.q))
digits = max(len(str(abs(int(q.p)))) + len(str(int(q.q))) for q in cs)
def horner(dps):
    mp.mp.dps = dps; g = mp.zeta(S); s = mp.mpf(0)
    for q in reversed(cs): s = s*g + mp.mpf(int(q.p))/mp.mpf(int(q.q))
    return s
v1, v2 = horner(digits+100), horner(digits+300)
assert v2 > 0 and abs(v1-v2) < abs(v2)*mp.mpf(10)**-30
logD = mp.log(v2); logc = mp.log(int(num_g)) - mp.log(int(den_l)); K2 = K*K
print(f"zeta{S} {MODE:5s} K={K} N={N} c={c} h={h}  real logΔ/K²={mp.nstr(logD/K2,6)}  clearing={mp.nstr(-logc/K2,6)}  ledger={mp.nstr((logD-logc)/K2,6)}")
if "--quad" in sys.argv:
    mp.mp.dps = 30
    f = lambda y: 1/(mp.exp(2*mp.pi*y)-1)
    w = lambda y: 2*y**S*mp.diff(f, y, S-1)/mp.factorial(S-1)
    for n in big[:2]:
        a = mp.mpf(n)/2
        lhs = mp.quad(lambda y: w(y)/(y*y + a*a), [0, 1, 4, 20])
        rhs = a**(S-1)*mp.zeta(S, a) - 1/(2*a) - mp.mpf(1)/(S-1)
        print(f"  --quad a={mp.nstr(a,4)}: {mp.nstr(lhs,20)} vs {mp.nstr(rhs,20)}  rel {mp.nstr(abs(lhs-rhs)/abs(rhs),3)}")
if "--ranges" in sys.argv:
    def vpq(q, p):
        v = 0; n = int(q.p); d = int(q.q)
        while n % p == 0: n //= p; v += 1
        while d % p == 0: d //= p; v -= 1
        return v
    nz = [q for q in cs if q != 0]; rng = {"p=2": 0.0, "3<=p<=K/3": 0.0, "K/3<p<=K": 0.0, "K<p<=2K": 0.0, "p>2K": 0.0}
    for p in primerange(2, 16*K*K+2):
        v = min(vpq(q, p) for q in nz)
        if v:
            key = "p=2" if p == 2 else ("3<=p<=K/3" if 3*p <= K else ("K/3<p<=K" if p <= K else ("K<p<=2K" if p <= 2*K else "p>2K")))
            rng[key] += -v*math.log(p)/K2
    print("  clearing by range: " + "  ".join(f"{k}: {v:+.4f}" for k, v in rng.items()))
