# Theorem D quadratic: floor(alpha^(c^n+s)) composite i.o.; floor = tr + eps. Check: for which (a,b,c,s>=4) do the first N values have a composite. (sanity, not a proof)
from sympy import isprime
import itertools
def trpow(a,b,N):
    # V_N with V0=2, V1=a, V_{k+2}=a V_{k+1} - b V_k ; tr C^N
    x,y=2,a
    # fast doubling via matrix
    def mul(X,Y): return [[X[0][0]*Y[0][0]+X[0][1]*Y[1][0],X[0][0]*Y[0][1]+X[0][1]*Y[1][1]],[X[1][0]*Y[0][0]+X[1][1]*Y[1][0],X[1][0]*Y[0][1]+X[1][1]*Y[1][1]]]
    R=[[1,0],[0,1]]; A=[[a,-b],[1,0]]
    while N:
        if N&1: R=mul(R,A)
        A=mul(A,A); N>>=1
    return R[0][0]+R[1][1]
import math
cases=0; allprime=0
for a in range(-6,7):
    for b in range(-6,7):
        D=a*a-4*b
        if b==0 or D<=0 or int(math.isqrt(D))**2==D: continue
        al=(abs(a)+math.sqrt(D))/2; be=b/ (a/abs(a)*al) if a!=0 else None
        roots=[(a+math.sqrt(D))/2,(a-math.sqrt(D))/2]
        big=[r for r in roots if abs(r)>1]; small=[r for r in roots if abs(r)<1]
        if len(big)!=1 or len(small)!=1 or big[0]<1: continue
        alpha,beta=big[0],small[0]
        for c in [2,3,5,7]:
            if b%c==0: continue
            for s in [4,5]:
                cases+=1
                vals=[]
                for n in range(1,7):
                    N=c**n+s; t=trpow(a,b,N)
                    eps = -1 if beta**N>0 else 0
                    vals.append(t+eps)
                if all(v>1 and isprime(v) for v in vals): allprime+=1; print("all prime n<=6:",a,b,c,s)
print("cases",cases,"with first 6 all prime:",allprime)
