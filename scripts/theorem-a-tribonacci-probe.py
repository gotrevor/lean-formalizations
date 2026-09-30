import sympy as sp
from sympy import Poly, isprime
X=sp.symbols('X')
t=[0,0,1]
for _ in range(20000): t.append(t[-1]+t[-2]+t[-3])
for c in [3,5,7,11,13,17,23]:
    irr=Poly(X**3-X**2-X-1,X,modulus=c).is_irreducible
    print(c,"irred",irr,"3|c-1",(c-1)%3==0,"trib(c^r) mod c r<3:",[t[c**r]%c if c**r<len(t) else None for r in range(3)])
# survivor sanity: small h, n up to 8 at c=3 -- count primes (not a proof, just sanity)
for h in range(-6,7):
    pr=[n for n in range(1,9) if 3**n<len(t) and t[3**n]+h>1 and isprime(t[3**n]+h)]
    print("h",h,"prime n:",pr)
