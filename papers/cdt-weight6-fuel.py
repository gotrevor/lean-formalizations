#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Weight-2k Beukers-type modular realizations of zeta(2k-1) alone, and their CDT 'fuel'.

For level N (X0(N) genus 0) build the Fricke Hauptmodul T = t + t∘w_N (t an eta-quotient
Hauptmodul of X0(N), pole at infinity).  H = E·(f - c) is single-valued near the w_N fixed point
i/sqrt(N); its singularities in u = T are the other cusps and the other w_N-coset elliptic points.
  disc fuel        = -log max_s |u_s - kappa|   (best integer kappa)
  univalent fuel  <= log(4 / diam S)           (equality when |S| = 2: a slit)
Also checks: a Fricke-eigen weight-2k Eisenstein combination with P(0)=P(2)=...=0, P(2k-1) != 0.
"""
import sys, itertools, math, cmath
import numpy as np
from sympy import divisors, Rational, Matrix, gcd

def eta(tau, terms=6000):
    q = np.exp(2j*np.pi*tau)
    n = np.arange(1, terms+1)
    return np.exp(2j*np.pi*tau/24) * np.prod(1 - q**n)

def etaq(r, tau):
    return np.prod([eta(d*tau)**e for d, e in r.items()])

def cusp_order(r, N, c):  # Ligozat: order of eta quotient at cusp with denominator c (c | N), in local param
    return Rational(N, 24) * sum(Rational(gcd(c, d)**2 * e, gcd(c, N//c) * c * d) for d, e in r.items())

def find_hauptmodul(N, R=None):
    ds = divisors(N)
    if R is None: R = 12 if len(ds) <= 4 else 6
    for ex in itertools.product(range(-R, R+1), repeat=len(ds)-1):
        r = dict(zip(ds[:-1], ex)); r[ds[-1]] = -sum(ex)
        if sum(d*e for d, e in r.items()) % 24 or sum((N//d)*e for d, e in r.items()) % 24: continue
        ords = {c: cusp_order(r, N, c) for c in ds}
        # cusp infinity <-> c = N ; width there is 1
        if ords[N] != -1 or any(ords[c] < 0 for c in ds if c != N): continue
        prod = 1
        for d, e in r.items(): prod *= Rational(d)**e
        if not prod.is_rational: continue
        return {d: e for d, e in r.items() if e}
    return None

def make_T(N, r):
    def t(tau): return etaq(r, tau)
    def T(tau): return t(tau) + t(-1/(N*tau))
    return T

def cusp_values(N, T, Y=25.0):
    vals = {}
    for c in divisors(N):
        if c in (1, N): continue          # cusps 0 and infinity: the pole of T
        tau = 1j*Y/(c*1j*Y + 1)            # gamma = [[1,0],[c,1]] applied to iY -> 1/c
        vals[f"cusp 1/{c}"] = T(tau)
    return vals

def elliptic_values(N, T, cmax=60):
    vals = []
    for c in range(1, cmax+1):
        for a in range(0, c):
            if (1 + N*a*a) % c: continue
            tau = a/c + 1j/(c*math.sqrt(N))
            vals.append(T(tau))
    # cluster
    reps = []
    for v in vals:
        if all(abs(v - w) > 1e-6*(1+abs(w)) for w in reps): reps.append(v)
    return reps

def eisenstein_ok(N, k):
    """Fricke-eigen combos sum c'_d G_d (G_d = d^{k/2} E_k(d tau)); P(s) = sum c'_d d^{k/2 - s}.
    Need P(0)=0 (no constant term) and P(2j)=0 for 1<=j<k/2-1 (kill pi-power periods); P(k-1)!=0."""
    ds = divisors(N); out = {}
    for eps in (+1, -1):
        pairs = [d for d in ds if d*d < N]; basis = []
        for d in pairs:
            v = {x: 0 for x in ds}; v[d] = 1; v[N//d] += eps; basis.append(v)
        if N in [d*d for d in ds]:
            v = {x: 0 for x in ds}; v[int(math.isqrt(N))] = 1
            if eps == 1: basis.append(v)
        P = lambda v, s: sum(Rational(v[d]) * Rational(d)**Rational(k, 2) / Rational(d)**s for d in ds)
        conds = [0] + [2*j for j in range(1, k//2 - 1 + 1) if 2*j < k - 1 and 2*j != k//2 or (2*j == k//2 and eps == 1)]
        conds = sorted(set(c for c in conds if c < k - 1))
        M = Matrix([[P(v, s) for v in basis] for s in conds]) if basis else Matrix([])
        ns = M.nullspace() if basis else []
        good = []
        for n in ns:
            comb = {d: sum(n[i]*basis[i][d] for i in range(len(basis))) for d in ds}
            if P(comb, k-1) != 0: good.append(comb)
        out[eps] = (len(basis), conds, len(good))
    return out

if __name__ == "__main__":
    k = int(sys.argv[1]); Ns = [int(x) for x in sys.argv[2:]]
    for N in Ns:
        r = find_hauptmodul(N)
        print(f"\n=== N={N}, weight {k}: Hauptmodul eta-quotient {r}")
        print("  Eisenstein (dim eigenspace, conditions P(s)=0 at s in, #solutions w/ P(k-1)!=0):", eisenstein_ok(N, k))
        if r is None: continue
        T = make_T(N, r)
        uell = T(1j/math.sqrt(N))
        cv = cusp_values(N, T); ev = [v for v in elliptic_values(N, T) if abs(v-uell) > 1e-6*(1+abs(uell))]
        print(f"  overconvergent elliptic i/sqrt(N): u = {uell:.6f}")
        for name, v in cv.items(): print(f"  {name}: u = {v:.6f}")
        for v in ev: print(f"  other elliptic: u = {v:.6f}")
        S = list(cv.values()) + ev
        if not S: print("  no other singularities?!"); continue
        D = max(abs(a-b) for a in S for b in S) if len(S) > 1 else 0.0
        kap = round(np.mean([s.real for s in S]))
        best = min(max(abs(s - kk) for s in S) for kk in range(kap-50, kap+51))
        print(f"  disc fuel (best integer shift) = {-math.log(best):.4f}")
        print(f"  univalent fuel upper bound log(4/diam) = {math.log(4/D) if D>0 else float('inf'):.4f}   (|S|={len(S)})")
