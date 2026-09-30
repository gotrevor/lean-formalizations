import random, sympy as sp
from sympy import Poly, GF
random.seed(7)
def mpow(A,e,m):
    R=sp.eye(A.rows); B=A.applyfunc(lambda x:x%m)
    while e:
        if e&1: R=(R*B).applyfunc(lambda x:x%m)
        B=(B*B).applyfunc(lambda x:x%m); e>>=1
    return R
X=sp.symbols('X')
tested=bad=bad_period=ctl=0
cases=[]
while len(cases)<150:
    d=random.choice([2,3,3,4,5]); c=random.choice([2,3,5,7])
    A=sp.Matrix(d,d,lambda i,j: random.randint(-4,4))
    if Poly(A.charpoly(X).as_expr(),X,modulus=c).is_irreducible: cases.append((A,c))
cases.append((sp.Matrix([[1,1,1],[1,0,0],[0,1,0]]),3))  # Tribonacci at 3
for A,c in cases:
    d=A.rows
    for n in range(0,4):
        m=c**(n+1); M=c**(n+2)
        S=sp.zeros(d,d)
        for k in range(d): S=S+mpow(A,c**(n+k),m)
        t=mpow(A,c**n,m).trace()
        D=(S-t*sp.eye(d)).applyfunc(lambda x:x%m)
        tested+=1
        if any(D): bad+=1
        if any((mpow(A,c**(n+d),m)-mpow(A,c**n,m)).applyfunc(lambda x:x%m)): bad_period+=1
        S2=sp.zeros(d,d)
        for k in range(d): S2=S2+mpow(A,c**(n+k),M)
        t2=mpow(A,c**n,M).trace()
        if any((S2-t2*sp.eye(d)).applyfunc(lambda x:x%M)): ctl+=1
# control 2: reducible charpoly should fail sometimes
red=0; redt=0
for _ in range(60):
    d=3;c=3;A=sp.Matrix(d,d,lambda i,j: random.randint(-4,4))
    if Poly(A.charpoly(X).as_expr(),X,modulus=c).is_irreducible: continue
    redt+=1; n=1; m=c**2
    S=sp.zeros(d,d)
    for k in range(d): S=S+mpow(A,c**(n+k),m)
    if any((S-mpow(A,c**n,m).trace()*sp.eye(d)).applyfunc(lambda x:x%m)): red+=1
print("tested",tested,"orbit-sum failures",bad,"period failures",bad_period,"| control: next precision fails",ctl,"| reducible fails",red,"/",redt)
