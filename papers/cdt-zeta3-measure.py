#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["mpmath", "numpy"]
# ///
"""CDT ICM Prop 2.4 irrationality measure for Apery's zeta(3), slit-plane template.
m <= I / (L - tau - (1-g)(c/mu - (1-g)/mu^2) log(1/rho)), c = 2 in CDT (c = 1 hypothetical).
Solve m = RHS for mu (the bound mu(eta) <= mu*)."""
from mpmath import mp, mpf, sqrt, log, findroot
mp.dps = 30
s2 = sqrt(2); beta = (s2+1)**4; alpha = (s2-1)**4

def classical(dec, grow, den):  # mu = 1 + (grow+den)/(dec-den): Q_n ~ e^{(grow+den)n}, |Q zeta - P| ~ e^{-(dec-den)n}
    return 1 + (grow+den)/(dec-den)

def mu_bound(L, I, tau, m, g, logrho_inv, c):
    D = I/m                                     # required denominator
    slack = L - tau - D
    if slack <= 0: return None                   # not even qualitative
    A = (1-g)*logrho_inv                         # slack = A (c/mu - (1-g)/mu^2)
    # A(1-g) t^2 - A c t + slack = 0, t = 1/mu ; take smallest t>0 -> largest mu? we need mu*: RHS(mu*)=m
    a, b, cc = A*(1-g), -A*c, slack
    disc = b*b - 4*a*cc
    if disc < 0: return mpf(1)                   # slack beats the whole penalty: only the trivial bound remains
    t = (-b - sqrt(disc))/(2*a)                  # smaller root t = 1/mu*
    return 1/t if t <= 1 else mpf(1)

# slit-plane template phi(z) = 4 beta z/(1+z)^2 ; rho = |z| with phi(z) = alpha (A,B singular there)
z = findroot(lambda z: 4*beta*z/(1+z)**2 - alpha, mpf('0.0002'))
L = log(4*beta); I = L                          # univalent: double integral = log|phi'(0)|
m, g, tau = 3, mpf(1)/3, mpf(24)/9
print(f"beta={float(beta):.6f} alpha={float(alpha):.6f} rho={float(z):.3e} log(1/rho)={float(-log(z)):.4f}")
print(f"Apery classical mu    = {float(classical(log(beta), log(beta), 3)):.4f}   (known 13.4178)")
print(f"CDT Prop 2.4 (c=2)    = {float(mu_bound(L, I, tau, m, g, -log(z), 2)):.4f}")
print(f"hypothetical c=1      = {float(mu_bound(L, I, tau, m, g, -log(z), 1)):.4f}")
# fuel L (univalent, I = L) each variant would need for Rhin-Viola, with rho and module held fixed
for c in (2, 1):
    for target in (13.4178, 5.513891):
        lo, hi = mpf(3), mpf(200)
        for _ in range(200):
            mid = (lo+hi)/2; v = mu_bound(mid, mid, tau, m, g, -log(z), c)
            if v is None or v > target: lo = mid
            else: hi = mid
        print(f"c={c}: fuel needed for mu <= {target}: L = {float(hi):.3f} (slit plane has {float(L):.3f})")

# ---- template scoring: Koebe (univalent) vs CDT bivalent 8(z+z^3)/(1+z)^4 (Rem 2.11.1), scaled by beta
import numpy as np
def dbl_integral(phi, K=4000):
    th = 2*np.pi*(np.arange(K)+0.5)/K
    z = np.exp(1j*th); v = phi(z)
    tot = 0.0
    for i in range(K):                      # off-diagonal mean of log|phi(z)-phi(w)| (log singularity integrable)
        d = np.abs(v[i] - v); d[i] = 1.0
        tot += np.sum(np.log(d))
    return tot/(K*(K-1))
koebe = lambda z: 4*z/(1+z)**2
biv   = lambda z: 8*(z+z**3)/(1+z)**4
from math import pi, log as flog
G = 0.915965594177219
print("\ncontrols: Koebe dbl-int =", round(dbl_integral(koebe), 4), "(expect log 4 =", round(flog(4), 4), ")",
      "  bivalent =", round(dbl_integral(biv), 4), "(CDT: log 8 + 4G/pi =", round(flog(8)+4*G/pi, 4), ")")
lb = float(log(beta))
for name, d0, I0 in (("Koebe", 4, flog(4)), ("bivalent", 8, flog(8)+4*G/pi)):
    Lt, It = flog(d0) + lb, I0 + lb
    rho_t = float(alpha)/(d0*float(beta))                   # first-order preimage of alpha
    mu_t = mu_bound(mpf(Lt), mpf(It), tau, m, g, mpf(-flog(rho_t)), 2)
    mu_t1 = mu_bound(mpf(Lt), mpf(It), tau, m, g, mpf(-flog(rho_t)), 1)
    print(f"{name:9s} L={Lt:.4f} dblint={It:.4f} log(1/rho)={-flog(rho_t):.4f}  mu(c=2)={float(mu_t):.4f}  mu(c=1)={float(mu_t1):.4f}")
