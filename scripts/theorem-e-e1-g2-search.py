import sys; B=float(sys.argv[1])
# E1 at g=2, s>0: find beta in O_K (K = conductor-13 cubic, x^3+x^2-4x+1) Pisot with beta<9,
# beta totally positive, beta/d a square in K for d in {2,13,26}.  Known-answer control: d=1 (beta = gamma^2).
import itertools, math
from fractions import Fraction as Fr
import numpy as np
r=sorted(np.roots([1,1,-4,1]).real)  # three real embeddings of theta
V=np.array([[1,t,t*t] for t in r])
Vi=np.linalg.inv(V)
def emb(a,b,c): return [a+b*t+c*t*t for t in r]
# box: one embedding in (1,9), other two in (-1,1); try each embedding as the Pisot one
cands=set()
for big in range(3):
    lo=[-1,-1,-1]; hi=[1,1,1]; lo[big]=1; hi[big]=B
    # coefficient bounds from Vi * box
    bnds=[]
    for i in range(3):
        m=sum(min(Vi[i][j]*lo[j],Vi[i][j]*hi[j]) for j in range(3)); M=sum(max(Vi[i][j]*lo[j],Vi[i][j]*hi[j]) for j in range(3))
        bnds.append(range(math.floor(m)-1, math.ceil(M)+2))
    for a,b,c in itertools.product(*bnds):
        e=emb(a,b,c)
        if 1<e[big]<B and all(abs(e[j])<1 for j in range(3) if j!=big): cands.add((a,b,c,big))
print("Pisot candidates <9:",len(cands))
# multiplication in K: theta^3 = -theta^2+4theta-1
def mul(x,y):
    p=[Fr(0)]*5
    for i in range(3):
        for j in range(3): p[i+j]+=x[i]*y[j]
    for k in (4,3):
        c=p[k]; p[k]=0; p[k-1]+=-c; p[k-2]+=4*c; p[k-3]+=-c
    return p[:3]
hits={1:[],2:[],13:[],26:[]}
for (a,b,c,big) in cands:
    e=emb(a,b,c)
    for d in hits:
        if min(e)<=0: continue
        rt=[math.sqrt(x/d) for x in e]
        for sg in itertools.product([1,-1],repeat=3):
            g=Vi@np.array([s_*x for s_,x in zip(sg,rt)])
            for den in (1,2,13,26):
                gg=[Fr(round(x*den),den) for x in g]
                if max(abs(float(gg[i])-g[i]) for i in range(3))<1e-7:
                    sq=mul(gg,gg)
                    if [d*x for x in sq]==[Fr(a),Fr(b),Fr(c)]:
                        hits[d].append(((a,b,c),e[big],gg)); break
for d,h in hits.items():
    print("d=",d,"count",len(h), [ (x[0],round(x[1],4)) for x in h[:6]])
