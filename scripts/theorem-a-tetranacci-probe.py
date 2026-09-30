import sympy as sp
from sympy import Poly
X=sp.symbols('X')
A=sp.Matrix([[1,1,1,1],[1,0,0,0],[0,1,0,0],[0,0,1,0]])
t=[0,0,0,1]
for _ in range(400): t.append(t[-1]+t[-2]+t[-3]+t[-4])
for N in range(1,7): assert (A**N)[3,0]==t[N], (N,(A**N)[3,0],t[N])
for c in [2,3,5,7,11,13]:
    irr=Poly(X**4-X**3-X**2-X-1,X,modulus=c).is_irreducible
    mu = c==2 or all((c-1)%k for k in (3,4))
    print(c,"irred",irr,"mu ok",mu,"T4(c^r) mod c r<4:",[t[c**r]%c if c**r<len(t) else (A**(c**r))[3,0]%c for r in range(4)])
