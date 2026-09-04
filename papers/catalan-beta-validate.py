#!/usr/bin/env -S uv run --quiet --with mpmath --with sympy python3
"""Numerically validate the exact statements to be frozen for Zudilin-2019 §2 (beta values).
(a) partial fractions a_{i,k} of R_n and d_n^{s-i} a_{i,k} in Z
(b) r_n = sum_{i even} A_i beta(i) + A_0 with A_i = 2^i sum_k (-1)^{k-1} a_{i,k}, odd-i A_i = 0,
    A_0 = explicit finite sums (derived below)
(c) integral representation (s=3, n=2) numerically
"""
import sympy as sp, mpmath as mp
from fractions import Fraction as Q
from math import lcm, factorial
t=sp.symbols('t')
def R_expr(n,s):
    num=2**(6*n)*sp.factorial(n)**(s-3)*(2*t+n)*sp.prod([t-n+j-sp.Rational(1,2) for j in range(1,3*n+1)])
    den=sp.prod([(t+j)**s for j in range(0,n+1)])
    return num/den
def dn(n):
    L=1
    for k in range(1,n+1): L=lcm(L,k)
    return L
def beta(i): return mp.nsum(lambda k: (-1)**int(k)/(2*k+1)**i,[0,mp.inf])
mp.mp.dps=30
for (n,s) in [(2,5),(4,5),(2,7),(4,7),(6,7)]:
    R=R_expr(n,s); pf=sp.apart(R,t)
    # extract a_{i,k}: coefficient of 1/(t+k)^i
    a={}
    for term in sp.Add.make_args(pf):
        c,rest=term.as_coeff_Mul()
        b,e=rest.as_base_exp()
        assert e<0 and b.is_polynomial(t) and sp.degree(b,t)==1, term
        k=int(b.subs(t,0)); i=int(-e); a[(i,k)]=Q(str(sp.nsimplify(c)))
    # (a) integrality
    ok=all((a[(i,k)]*dn(n)**(s-i)).denominator==1 for (i,k) in a)
    # (b) decomposition
    m=n//2
    def S(i,k):  # sum_{nu>=-m-1} (-1)^nu/(nu+k-1/2)^i  as (coef of 2^i beta(i), rational part)
        # = (-1)^{k-1} sum_{l>=k-m-2} (-1)^l/(l+1/2)^i
        sgn=-1 if (k-1)%2 else 1; lo=k-m-2
        rat=Q(0)
        if lo<0:
            for l in range(lo,0):
                j=-l-1; rat+=Q((-1)**(j+1)*(-1)**i)/(Q(2*j+1,2)**i)
        else:
            for l in range(0,lo):
                rat-=Q((-1)**l)/(Q(2*l+1,2)**i)
        return sgn, Q(sgn)*rat
    A={}; A0=Q(0)
    for (i,k),c in a.items():
        sgn,rat=S(i,k); A[i]=A.get(i,Q(0))+c*sgn*2**i; A0+=c*rat
    rn_direct=mp.nsum(lambda nu: (-1)**int(nu)*mp.mpf(R.subs(t,mp.mpf(nu)-mp.mpf(1)/2)) if True else 0,[1,mp.inf]) if False else None
    Rf=sp.lambdify(t,R,'mpmath')
    rn_direct=mp.nsum(lambda nu: (-1)**int(nu)*Rf(mp.mpf(int(nu))-mp.mpf(1)/2),[n+1,mp.inf])
    rn_dec=mp.mpf(A0.numerator)/A0.denominator+sum(mp.mpf(A[i].numerator)/A[i].denominator*beta(i) for i in A if i%2==0)
    odd_zero=all(A[i]==0 for i in A if i%2==1)
    denA=[ (A[i]*dn(n)**(s-i)).denominator for i in sorted(A) if i%2==0 ]
    denA0=(A0*dn(n)**s).denominator
    print(f"n={n} s={s}: (a) d^(s-i)a_ik int:{ok}  (b) odd A_i=0:{odd_zero}  r_n direct={mp.nstr(rn_direct,12)} decomp={mp.nstr(rn_dec,12)} rel={mp.nstr(abs(rn_direct-rn_dec)/abs(rn_direct),3)}  d^(s-i)A_i dens={denA} d^s A_0 den={denA0}")
# (c) integral representation, s=3 n=2
n,s=2,3
Rf=sp.lambdify(t,R_expr(n,s),'mpmath')
rn=mp.nsum(lambda nu: (-1)**int(nu)*Rf(mp.mpf(int(nu))-mp.mpf(1)/2),[n+1,mp.inf])
mp.mp.dps=12
pref=mp.mpf(2)**(6*n)*mp.factorial(3*n+1)/mp.factorial(n)**3
f=lambda t1,t2,t3: (1-t1*t2*t3)*(t1*t2*t3)**(n-mp.mpf(1)/2)*((1-t1)*(1-t2)*(1-t3))**n/(1+t1*t2*t3)**(3*n+2)
I=mp.quad(f,[0,1],[0,1],[0,1])
print(f"(c) s=3 n=2: r_n={mp.nstr(rn,10)}  integral formula={mp.nstr(pref*I,10)}  ratio={mp.nstr(rn/(pref*I),8)}")
