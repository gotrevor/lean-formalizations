# mixed-unit examples: f = X^2 - 3X - 2 at c=2 (f ≡ X(X+1) mod 2); cubic X^3-2X^2-2? check Pisot & mixed. Count primes among floor(alpha^(c^n+s)), n<=7.
import numpy as np, math
from sympy import isprime
def floors(coeffs,c,s,nmax):
    # coeffs: monic f = X^d + ... ; use companion trace + sign of delta via numpy roots
    r=np.roots(coeffs); big=max(r,key=abs).real
    d=len(coeffs)-1
    A=np.zeros((d,d),dtype=object)
    for j in range(d): A[0][j]=-coeffs[j+1]
    for i in range(1,d): A[i][i-1]=1
    out=[]
    for n in range(1,nmax+1):
        N=c**n+s
        M=np.identity(d,dtype=object); B=A.copy(); e=N
        while e:
            if e&1: M=M.dot(B)
            B=B.dot(B); e>>=1
        tr=sum(M[i][i] for i in range(d))
        delta=sum((x**N) for x in r if abs(x)<1).real
        out.append(int(tr) - (1 if delta>0 else 0))
    return big,out
for coeffs,c,s in [([1,-3,-2],2,4),([1,-3,-2],2,5),([1,-2,0,-2],2,5),([1,-4,2,-2],2,5)]:
    r=np.roots(coeffs)
    pis=sorted(abs(r))
    big,vals=floors(coeffs,c,s,7)
    print(coeffs,"moduli",np.round(pis,3),"c",c,"s",s,"prime flags",[isprime(v) for v in vals])
