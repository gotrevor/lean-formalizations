# Phase E5 probe: lower-bound sieve from ONE Buchstab step (from w=2) on Selberg's Lambda^2 upper bound.
# f1(s) = 1 - (1/s) int_{s-1}^inf (F_S(t)-1) dt, F_S(t) = e^gamma / int_0^{t/2} rho.  Control column: JR f(s) = 2e^gamma log(s-1)/s.
# Finding: f1 < 0 for s <= ~2.05 (f1(2.05) = -0.003), so the one-step route cannot reach every s > 2.
import math
h=1e-3; N=int(40/h)
rho=[1.0]*N; m=int(1/h)
for i in range(1,N):
    u=i*h
    rho[i]=rho[i-1]-(h*rho[i-m]/u if u>1 else 0)
g=[0.0]*N; acc=0
for i in range(N): acc+=rho[i]*h; g[i]=acc
eg=math.exp(0.5772156649)
F=lambda x: eg/g[min(int(x/2/h),N-1)]
for s in [2.02,2.05,2.1,2.3,2.5,3,4]:
    val=0; x=s-1
    while x<39: val+=(F(x)-1)*1e-3; x+=1e-3
    print(s, 1-val/s, 2*eg*math.log(s-1)/s)
