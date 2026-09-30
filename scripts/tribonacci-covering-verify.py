def mul(X,Y,p): return [[sum(X[i][k]*Y[k][j] for k in range(3))%p for j in range(3)] for i in range(3)]
def mpow(A,e,p):
    R=[[int(i==j) for j in range(3)] for i in range(3)]
    while e:
        if e&1: R=mul(R,A,p)
        A=mul(A,A,p); e>>=1
    return R
A=[[1,1,1],[1,0,0],[0,1,0]]
cert={-3:53,-2:5,-1:7,0:13,1:593,2:47,3:5}
ok=True
for k in range(0,6):
    n=95+1980*k
    for h,p in cert.items():
        if (mpow(A,3**n,p)[2][0]+h)%p: ok=False; print("FAIL",k,h,p)
# control: a wrong offset should fail
bad=sum(1 for h,p in cert.items() if (mpow(A,3**96,p)[2][0]+h)%p)
print("verified k<6:",ok,"| control n=96 failures:",bad)
