#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Check the shifted, ratio-free reformulation of R_n that will be FROZEN in Lean.

Lean definition to freeze (u = nu - n - 1 >= 0, so nu = n+1+u):

  Rval s n u = 2^(6n) * (n!)^(s-3) * (3n+1+2u) * ((u+3n)!/u!)
               / prod_{j=0}^{n} ( (2*(n+1+u+j) - 1)/2 )^s

  rForm s n = sum_{u>=0} (-1)^(n+u+1) * Rval s n u

against the source form  r_n = sum_{nu>=1} (-1)^nu R_n(nu-1/2).
"""
from mpmath import mp, mpf, factorial
mp.dps = 60

def R(n, s, t):
    num = mpf(2)**(6*n) * factorial(n)**(s-3) * (2*t+n)
    for j in range(1, 3*n+1): num *= (t - n + j - mpf(1)/2)
    den = mpf(1)
    for j in range(0, n+1): den *= (t + j)**s
    return num/den

def Rval(s, n, u):
    num = mpf(2)**(6*n) * factorial(n)**(s-3) * (3*n+1+2*u) * factorial(u+3*n)/factorial(u)
    den = mpf(1)
    for j in range(0, n+1): den *= (mpf(2*(n+1+u+j)-1)/2)**s
    return num/den

def src(n, s, terms=4000):
    return sum((-1)**nu * R(n, s, nu - mpf(1)/2) for nu in range(1, terms))

def new(n, s, terms=4000):
    return sum((-1)**(n+u+1) * Rval(s, n, u) for u in range(0, terms))

for (n, s) in [(2,5),(4,5),(2,7),(4,7),(6,7),(2,21),(4,21),(6,21)]:
    a, b = src(n, s), new(n, s)
    # also check termwise identity nu = n+1+u
    tw = max(abs(R(n,s,(n+1+u)-mpf(1)/2) - Rval(s,n,u)) for u in range(0,8))
    print(f"n={n} s={s:2d}  src={mp.nstr(a,12)}  new={mp.nstr(b,12)}  match={abs(a-b) <= mpf(10)**-30*max(abs(a),1)}  termwise_maxdiff={mp.nstr(tw,3)}")
