#!/usr/bin/env -S uv run --quiet python3
# Eskandari-Murty-Nemoto (arXiv:2510.20648) pole-reduction probe for Catalan forms a + bG.
# Written 2026-09-04 by a sibling Ren session (originally /private/tmp/catalan_motive_probe.py);
# preserved here.  Research record: KB reference/2026-09-04-catalan-three-proof-paths.md
from fractions import Fraction as Q
from math import comb, gcd, log
from decimal import Decimal, getcontext

getcontext().prec = 80
G = Decimal("0.91596559417721901505460351493238411077414937428167213426649811962176301977625477")

def pmul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def ppow(a,n):
    r=[Q(1)]
    while n:
        if n&1:r=pmul(r,a)
        a=pmul(a,a);n//=2
    return r
def pint01(a): return sum(x/Q(i+1) for i,x in enumerate(a))
def padd(a,b,scale=Q(1)):
    c=[Q(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=scale*x
    return c

def cpow(k, sign):
    # (1-y + sign*i*y)^k, coefficients are Gaussian rationals.
    base=[(Q(1),Q(0)),(Q(-1),Q(sign))]
    r=[(Q(1),Q(0))]
    for _ in range(k):
        c=[(Q(0),Q(0))]*(len(r)+1)
        for i,(ar,ai) in enumerate(r):
            for j,(br,bi) in enumerate(base):
                cr,ci=c[i+j]
                c[i+j]=(cr+ar*br-ai*bi,ci+ar*bi+ai*br)
        r=c
    return r
def cmul(a,b):
    c=[(Q(0),Q(0))]*(len(a)+len(b)-1)
    for i,(ar,ai) in enumerate(a):
        for j,(br,bi) in enumerate(b):
            cr,ci=c[i+j]
            c[i+j]=(cr+ar*br-ai*bi,ci+ar*bi+ai*br)
    return c

def Joff(k,l):
    p=cmul(cpow(k,1),cpow(l,-1)); q=cmul(cpow(l,1),cpow(k,-1))
    # i*(p-q): real coefficient is -(imaginary difference)
    h=[-(a[1]-b[1]) for a,b in zip(p,q)]
    # Exact division by 2y(1-y), then multiply by 2y-1.
    # h has zero constant and h(1)=0. Divide by y then (1-y).
    v=h[1:]
    quotient=[]; accum=Q(0)
    # v=(1-y)*quotient: v_i=q_i-q_{i-1}
    for vi in v[:-1]:
        accum += vi; quotient.append(accum)
    assert v[-1] == -accum
    integrand=pmul(quotient,[Q(-1,2),Q(1)])
    return pint01(integrand)/Q(k-l)

def Jdiag(k):
    q=[Q(1),Q(-2),Q(2)]
    power=[Q(1)]; total=[Q(0)]
    for j in range(k):
        total=padd(total,power,Q(1,j+1)); power=pmul(power,q)
    return -pint01(total)/2

def lcm(a,b): return a//gcd(a,b)*b
def monomial(n):
    b=Q(comb(2*n,n),2**(4*n))
    a=b*Jdiag(2*n)
    for r in range(n):
        k,l=4*n-2*r,2*r
        lam=Q(((-1)**(n+r))*comb(2*n,r),2**(4*n))
        a += lam*Joff(k,l)
    D=lcm(a.denominator,b.denominator)
    val=Decimal(a.numerator)/Decimal(a.denominator)+(Decimal(b.numerator)/Decimal(b.denominator))*G
    return a,b,D,val*Decimal(D)

def high_pole(n):
    # I_n = int_Delta x^(4n)y^(4n)/(1-x^2-y^2)^(2n+1) dxdy.
    # Apply Lemma 9.2.3(c) and the explicit boundary term in Lemma 9.3.1
    # n times, ending at the simple-pole monomial x^(2n)y^(2n).
    a,b,_,_=monomial(n)
    m=2*n
    for t in range(2,2*n+1,2):
        # Reverse one reduction: current exponents m+2 and pole index t.
        m += 2
        d=m-t
        c=Q((m-1)**2,4*t*(t-1))
        boundary=-Q(1,4*t*(t-1)*2**(t-1)*comb(2*d,d))
        a,b=boundary+c*a,c*b
    D=lcm(a.denominator,b.denominator)
    val=Decimal(a.numerator)/Decimal(a.denominator)+(Decimal(b.numerator)/Decimal(b.denominator))*G
    return a,b,D,val*Decimal(D)

print("simple-pole family F=x^(2n)y^(2n)")
for n in range(1,11):
    a,b,D,L=monomial(n)
    root=float(abs(L))**(1/(4*n))
    print(n, f"deg={4*n:2d}", f"Ddigits={len(str(D))}", f"cleared={float(L):.6g}", f"perdeg={root:.6f}")
print("high-pole family F=x^(4n)y^(4n), t=2n")
for n in range(1,31):
    a,b,D,L=high_pole(n)
    root=float(abs(L))**(1/n)
    print(n, f"deg={8*n:3d}", f"Ddigits={len(str(D))}", f"cleared={float(L):.8g}", f"per-n={root:.6f}", f"a={a}",f"b={b}")
