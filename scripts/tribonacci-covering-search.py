import sys, itertools
from sympy import primerange, factorint
from sympy.ntheory.modular import crt
from math import lcm
H=int(sys.argv[1]); MMAX=int(sys.argv[2]); PMAX=int(sys.argv[3])
def mul(X,Y,p): return [[sum(X[i][k]*Y[k][j] for k in range(3))%p for j in range(3)] for i in range(3)]
def mpow(A,e,p):
    R=[[int(i==j) for j in range(3)] for i in range(3)]
    while e:
        if e&1: R=mul(R,A,p)
        A=mul(A,A,p); e>>=1
    return R
A=[[1,1,1],[1,0,0],[0,1,0]]; I=[[1,0,0],[0,1,0],[0,0,1]]
def order(p):
    M=(p**3-1)*(p**2-1)*(p-1)*p  # multiple of the order (|GL3| divides p^3 * that)
    M*=p*p
    o=M
    for q in factorint(M):
        while o%q==0 and mpow(A,o//q,p)==I: o//=q
    return o
opts={h:[] for h in range(-H,H+1)}
for p in primerange(5,PMAX):
    if p in (3,11): continue
    o=order(p); v=0; oo=o
    while oo%3==0: oo//=3; v+=1
    j=1
    if oo>1:
        while pow(3,j,oo)!=1: j+=1
    for m in range(max(v,1),MMAX+1):
        r=mpow(A,3**m,p)[2][0]
        for h in range(-H,H+1):
            if (r+h)%p==0: opts[h].append((m%j,j,p,m))
for h in opts: opts[h]=sorted(set(opts[h]),key=lambda t:t[1])[:12]
print({h:len(v) for h,v in opts.items()})
best=None
for combo in itertools.product(*[opts[h] for h in sorted(opts)]):
    res=crt([c[1] for c in combo],[c[0] for c in combo])
    if res is not None:
        L=lcm(*[c[1] for c in combo])
        if best is None or L<best[0]: best=(L,res[0],combo)
        break
print(best)
