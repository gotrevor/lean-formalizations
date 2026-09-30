import sympy as sp
th=sp.symbols('t'); f=th**3+th**2-4*th+1
def trpow(a,b,c,N):
    # multiplication matrix of beta=a+b t+c t^2 on basis 1,t,t^2 mod f
    cols=[]
    for e in (1,th,th**2):
        r=sp.Poly(sp.rem(sp.expand((a+b*th+c*th**2)*e),f,th),th)
        cols.append([r.coeff_monomial(th**i) for i in range(3)])
    M=sp.Matrix(cols).T
    return (M**N).trace()
for (d,beta) in [(13,(5,-20,12)),(2,(212,-74,-58)),(26,(10,-40,24)),(1,(41,-14,-11))]:
    vals=[trpow(*beta,N) for N in range(1,8)]
    print(d,beta,[sp.factorint(v) if abs(v)<10**30 else '...' for v in vals[:4]], 'gcd-q check:', all(v%(2 if d%2==0 else 13 if d==13 else 1)==0 for v in vals))
