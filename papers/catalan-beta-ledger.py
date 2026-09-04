#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Ledger probe for Zudilin's (2019, arXiv:1804.09922) linear forms in even beta values.

R_n(t) = 2^{6n} n!^{s-3} (2t+n) prod_{j=1}^{3n} (t-n+j-1/2) / prod_{j=0}^{n} (t+j)^s,   s odd, n even,
r_n = sum_{nu>=1} (-1)^nu R_n(nu-1/2)  =  sum_i a_i beta(i) + a_0,   d_n^{s-i} Phi_n^{-1} a_i in Z.

We measure, per odd s:
  L_s     = lim r_n^{1/n} from Zudilin's (3): 12^3 max_t t^s(1-t)^s/(1+t^s)^3   (exact asymptotic)
  A_s(n)  = (sum_nu |R_n(nu-1/2)|)^{1/n}  the CRUDE absolute bound an elementary proof would use
  ledger  = log L + s   (no Phi saving; need < 0)   and   log L + s - kappa  (with Phi, kappa=0.94111)
  crude   = log A + s
"""
import sys
from mpmath import mp, mpf, log, exp, findroot, factorial, mpf as F
mp.dps = 40
kappa = mpf('0.9411124762')

def L_s(s):
    f = lambda t: t**s*(1-t)**s/(1+t**s)**3
    # maximise on (0,1): derivative zero; bracket-free: sample then refine
    best = max((f(mpf(i)/2000), mpf(i)/2000) for i in range(1, 2000))
    t0 = findroot(lambda t: mp.diff(f, t), best[1])
    return 1728*f(t0)

def R(n, s, t):
    num = mpf(2)**(6*n) * factorial(n)**(s-3) * (2*t+n)
    for j in range(1, 3*n+1): num *= (t - n + j - mpf(1)/2)
    den = mpf(1)
    for j in range(0, n+1): den *= (t + j)**s
    return num/den

def rates(n, s):
    r = mpf(0); a = mpf(0); nu = 1; last = None
    while True:
        v = R(n, s, nu - mpf(1)/2)
        r += (-1)**nu * v; a += abs(v)
        if nu > 3*n and abs(v) < mpf(10)**(-30) * a: break
        nu += 1
    return r, a

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    print(f"n={n}")
    for s in range(7, 42, 2):
        L = L_s(s); r, a = rates(n, s)
        lr = log(abs(r))/n; la = log(a)/n; lL = log(L)
        print(f"s={s:2d} | logL={float(lL):8.3f} log r^(1/n)={float(lr):8.3f} log A^(1/n)={float(la):8.3f} | "
              f"ledger noPhi={float(lL+s):7.3f} withPhi={float(lL+s-kappa):7.3f} crude noPhi={float(la+s):7.3f} | r_n>0:{r>0}")
