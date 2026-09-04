#!/usr/bin/env -S uv run --quiet --with mpmath --with numpy python3
"""Path-1 probe: positive linear forms in 1 and G from the Eskandari-Murty-Nemoto motive.

EMN (arXiv:2510.20648, Thm 1.1.1): for F in Q[x,y] fixed by sigma:(x,y)->(-y,x) and divisible
by x^{2ceil(t/2)} y^{2ceil(t/2)},
    I(F,t) := int_Delta F / (1 - x^2 - y^2)^{t+1} dxdy = a + b G,   a, b in Q,
Delta the simplex {x,y >= 0, x+y <= 1}.  This file makes their construction EXACT and general
(any sigma-invariant F, any t), validates every branch against high-precision quadrature, and
then runs the only search that is not Dirichlet-trivial:

  * F must be POSITIVE on Delta so that I(F,t) is *provably* small (an integral, not a value
    that happens to be small because G is what it is).  Take F = orbit-sum of h^2 under sigma.
  * Then I(F,t) = c^T Q c is a quadratic form in the coefficients c of h, and the Gram matrix
    Q = A + B G is itself EXACT (each entry is I(sigma-orbit-sum(m_i m_j), t)).
  * Minimising c^T Q c over integer c != 0 is a shortest-vector problem: LLL on Q.
  * For each short vector report the exact (a,b), the exact denominator D, and
    log10(D * I).  The proof closes iff this can be driven to -infinity along a family.

Usage:
  catalan-emn-search.py validate            # exact evaluator vs quadrature, every branch
  catalan-emn-search.py scan [Nmax] [tmax]  # the search; prints one line per (N,t)
"""
from __future__ import annotations
import sys
from fractions import Fraction as Q
from math import comb, lcm, log10
from itertools import product

# ---------------------------------------------------------------- polynomials in x,y over Q
# dict {(p,q): Fraction} meaning sum c x^p y^q
def padd(*ps):
    r = {}
    for p in ps:
        for k, v in p.items():
            r[k] = r.get(k, Q(0)) + v
    return {k: v for k, v in r.items() if v != 0}

def pscale(p, s):
    return {k: v * s for k, v in p.items() if v * s != 0}

def pmul(p, q):
    r = {}
    for (a, b), u in p.items():
        for (c, d), v in q.items():
            r[(a + c, b + d)] = r.get((a + c, b + d), Q(0)) + u * v
    return {k: v for k, v in r.items() if v != 0}

def pdeg(p):
    return max((a + b for (a, b) in p), default=-1)

def sigma(p):
    """(x,y) -> (-y, x):  x^a y^b -> (-y)^a x^b = (-1)^a x^b y^a."""
    r = {}
    for (a, b), v in p.items():
        r[(b, a)] = r.get((b, a), Q(0)) + v * (-1) ** a
    return {k: v for k, v in r.items() if v != 0}

def orbit_sum(p):
    s1 = sigma(p); s2 = sigma(s1); s3 = sigma(s2)
    return padd(p, s1, s2, s3)

def is_sigma_invariant(p):
    return sigma(p) == p

def divisible_by_xy_pow(p, c):
    return all(a >= c and b >= c for (a, b) in p)

# EMN Notation 9.2.1:  D1 F = d/dx (F/x),  D2 F = d/dy (F/y)  (on polynomials divisible by x, y)
def D1(p):
    r = {}
    for (a, b), v in p.items():
        assert a >= 1
        if a - 1 >= 1:
            r[(a - 2, b)] = r.get((a - 2, b), Q(0)) + v * (a - 1)
    return {k: v for k, v in r.items() if v != 0}

def D2(p):
    r = {}
    for (a, b), v in p.items():
        assert b >= 1
        if b - 1 >= 1:
            r[(a, b - 2)] = r.get((a, b - 2), Q(0)) + v * (b - 1)
    return {k: v for k, v in r.items() if v != 0}

def dx(p):
    r = {}
    for (a, b), v in p.items():
        if a >= 1:
            r[(a - 1, b)] = r.get((a - 1, b), Q(0)) + v * a
    return {k: v for k, v in r.items() if v != 0}

def divide_xy_pow(p, c):
    assert divisible_by_xy_pow(p, c)
    return {(a - c, b - c): v for (a, b), v in p.items()}

def eval_line_int(p, param):
    """int_0^1 p(param(y)) dy exactly, where param is 'PQ' (x=1-y) or 'QP' (y=1-x, var x)."""
    # substitute and integrate a univariate polynomial exactly
    # (1-y)^a y^b  expands via binomial
    total = Q(0)
    for (a, b), v in p.items():
        if param == 'PQ':   # x = 1-y, y = y
            for j in range(a + 1):
                total += v * comb(a, j) * (-1) ** j / Q(b + j + 1)
        else:               # x = x, y = 1-x
            for j in range(b + 1):
                total += v * comb(b, j) * (-1) ** j / Q(a + j + 1)
    return total

# ---------------------------------------------------------------- t = 0: EMN §8 exactly
# Gaussian rationals as (re, im) Fractions
def gmul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])

def zw_expand(p):
    """Coefficients lambda_{k,l} of F((z+w)/2, (z-w)/(2i)) in z^k w^l (Gaussian rationals)."""
    # x = (z+w)/2 ; y = (z-w)/(2i) = -i(z-w)/2 = (-i/2) z + (i/2) w
    X = {(1, 0): (Q(1, 2), Q(0)), (0, 1): (Q(1, 2), Q(0))}
    Y = {(1, 0): (Q(0), Q(-1, 2)), (0, 1): (Q(0), Q(1, 2))}
    def gpmul(a, b):
        r = {}
        for ka, va in a.items():
            for kb, vb in b.items():
                k = (ka[0] + kb[0], ka[1] + kb[1])
                w = gmul(va, vb)
                o = r.get(k, (Q(0), Q(0)))
                r[k] = (o[0] + w[0], o[1] + w[1])
        return r
    powX = [{(0, 0): (Q(1), Q(0))}]
    powY = [{(0, 0): (Q(1), Q(0))}]
    N = pdeg(p)
    for _ in range(N):
        powX.append(gpmul(powX[-1], X)); powY.append(gpmul(powY[-1], Y))
    out = {}
    for (a, b), v in p.items():
        term = gpmul(powX[a], powY[b])
        for k, w in term.items():
            o = out.get(k, (Q(0), Q(0)))
            out[k] = (o[0] + v * w[0], o[1] + v * w[1])
    return {k: w for k, w in out.items() if w != (Q(0), Q(0))}

def J_off(k, l):
    """Lemma 8.2.1: int_Delta (z^k w^l + z^l w^k)/(1-zw) dxdy, k > l >= 0, k = l mod 4."""
    assert k > l and (k - l) % 4 == 0
    # f(x,y) = (x+iy)^k (x-iy)^l - (x+iy)^l (x-iy)^k ; integrand i f(1-y,y) (2y-1)/(2y(1-y))
    # Work with univariate polynomials in y with Gaussian-rational coefficients.
    def cpow(sign, e):  # (1-y + sign*i*y)^e as list of (re,im)
        base = [(Q(1), Q(0)), (Q(-1), Q(sign))]
        r = [(Q(1), Q(0))]
        for _ in range(e):
            c = [(Q(0), Q(0))] * (len(r) + 1)
            for i, u in enumerate(r):
                for j, v in enumerate(base):
                    w = gmul(u, v); c[i + j] = (c[i + j][0] + w[0], c[i + j][1] + w[1])
            r = c
        return r
    def cmul(a, b):
        c = [(Q(0), Q(0))] * (len(a) + len(b) - 1)
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                w = gmul(u, v); c[i + j] = (c[i + j][0] + w[0], c[i + j][1] + w[1])
        return c
    f = [(a[0] - b[0], a[1] - b[1]) for a, b in zip(cmul(cpow(1, k), cpow(-1, l)), cmul(cpow(1, l), cpow(-1, k)))]
    # i*f : (re,im) -> (-im, re); the paper says i f is real (im part 0)
    h = []
    for (re, im) in f:
        assert re == 0, "i*f should be real"
        h.append(-im)
    # divide h(y) by y (h(0)=0) then by (1-y) (h(1)=0)
    assert h[0] == 0
    v = h[1:]
    quot = []; acc = Q(0)
    for vi in v[:-1]:
        acc += vi; quot.append(acc)
    assert v[-1] == -acc, "f(1-y,y) must vanish at y=1"
    # multiply by (2y-1)/2 and integrate over [0,1]
    integrand = [Q(0)] * (len(quot) + 1)
    for i, c in enumerate(quot):
        integrand[i] += -c / 2; integrand[i + 1] += c
    val = sum(c / Q(i + 1) for i, c in enumerate(integrand))
    return val / (k - l)

def J_diag(k):
    """Lemma 8.2.3: int_Delta (z^k w^k - 1)/(1-zw) dxdy = -(1/2) int_0^1 sum_{j<k} (2y^2-2y+1)^j/(j+1) dy."""
    qpoly = [Q(1), Q(-2), Q(2)]
    power = [Q(1)]; total = [Q(0)]
    for j in range(k):
        total = [ (total[i] if i < len(total) else Q(0)) + (power[i] if i < len(power) else Q(0)) / (j + 1)
                  for i in range(max(len(total), len(power))) ]
        # power *= qpoly
        new = [Q(0)] * (len(power) + 2)
        for i, c in enumerate(power):
            for j2, d in enumerate(qpoly):
                new[i + j2] += c * d
        power = new
    return -sum(c / Q(i + 1) for i, c in enumerate(total)) / 2

def I_t0(p):
    """(a, b) with int_Delta F/(1-x^2-y^2) dxdy = a + b G, for sigma-invariant F (any tau-part)."""
    assert is_sigma_invariant(p)
    lam = zw_expand(p)
    b = Q(0); a = Q(0)
    for (k, l), (re, im) in lam.items():
        assert (k - l) % 4 == 0, "sigma-invariance forces k = l (mod 4)"
        if k == l:
            assert im == 0
            b += re
            a += re * J_diag(k) if k > 0 else 0
        elif k > l:
            # pair with (l,k): lambda_{lk} = conj(lambda_{kl}); real part -> Lemma 8.2.1,
            # imaginary part -> tau-odd, integrates to zero (EMN Remark 8.2.2 / 7.4.3)
            a += re * J_off(k, l)
    return a, b

# ---------------------------------------------------------------- t > 0: EMN §9 exactly
def I_t(p, t):
    """(a, b) with int_Delta F/(1-x^2-y^2)^{t+1} dxdy = a + b G.  Requires sigma-invariance and
    x^{2ceil(t/2)} y^{2ceil(t/2)} | F (Thm 1.1.1 (ii))."""
    assert is_sigma_invariant(p)
    c = 2 * ((t + 1) // 2)
    assert divisible_by_xy_pow(p, c), f"need x^{c} y^{c} | F"
    if t == 0:
        return I_t0(p)
    if t % 2 == 0:
        # Lemma 9.2.3(c): F/g^{t+1} = (1/(4t(t-1))) * [ d(theta) + D2D1F/g^{t-1} ]  with
        # int_Delta d(theta) = (9.4) + (9.5) = -(1/2^{t-1}) int_0^1 f_x(1-y,y) dy - f(Q)/2^{t-1},
        # F = x^t y^t f.
        f = divide_xy_pow(p, t)
        fx = dx(f)
        bnd = -eval_line_int(fx, 'PQ') / Q(2) ** (t - 1) - f.get((0, 0), Q(0)) * 0  # f(Q) below
        fQ = sum(v for (a_, b_), v in f.items() if a_ == 0)  # f(0,1)
        bnd -= fQ / Q(2) ** (t - 1)
        a2, b2 = I_t(D2(D1(p)), t - 2)
        s = Q(1, 4 * t * (t - 1))
        return s * (bnd + a2), s * b2
    else:
        # (9.6): F/g^{t+1} dxdy = (1/(4t)) [ d(F dy/(x g^t)) - d(F dx/(y g^t)) - (D1+D2)F/g^t dxdy ]
        # Lemma 9.4.1 with F = x^{t+1} y^{t+1} f:
        #   int d(F dy/(x g^t)) = (1/2^t) int_0^1 y f(1-y,y) dy
        #   int d(F dx/(y g^t)) = -(1/2^t) int_0^1 x f(x,1-x) dx    (orientation P->Q)
        f = divide_xy_pow(p, t + 1)
        yf = pmul(f, {(0, 1): Q(1)}); xf = pmul(f, {(1, 0): Q(1)})
        bnd = (eval_line_int(yf, 'PQ') + eval_line_int(xf, 'QP')) / Q(2) ** t
        a1, b1 = I_t(padd(D1(p), D2(p)), t - 1)
        s = Q(1, 4 * t)
        return s * (bnd - a1), -s * b1

# ---------------------------------------------------------------- numeric validator
def I_numeric(p, t, dps=30):
    import mpmath as mp
    mp.mp.dps = dps
    def F(x, y):
        return sum(float(v) * x ** a * y ** b for (a, b), v in p.items()) if False else \
               sum(mp.mpf(v.numerator) / v.denominator * x ** a * y ** b for (a, b), v in p.items())
    def inner(x):
        return mp.quad(lambda y: F(x, y) / (1 - x * x - y * y) ** (t + 1), [0, 1 - x])
    return mp.quad(inner, [0, 1])

def validate():
    import mpmath as mp
    mp.mp.dps = 30
    G = mp.catalan
    def mono(a, b): return {(a, b): Q(1)}
    cases = [
        ("x^2y^2, t=0 (paper: -5/48 + G/8)", mono(2, 2), 0),
        ("x^4y^4, t=0 (paper: -569/26880 + 3G/128)", mono(4, 4), 0),
        ("x^4y^4, t=2 (paper: -49/384 + 9G/64)", mono(4, 4), 2),
        ("orbit(x^4 y^0) = x^4+y^4, t=0", orbit_sum(mono(4, 0)), 0),
        ("orbit(x^3 y) tau-odd part, t=0", orbit_sum(mono(3, 1)), 0),
        ("orbit(x^6 y^2), t=0", orbit_sum(mono(6, 2)), 0),
        ("orbit(x^3 y^3) [t=1 needs x^2y^2 | F], t=1", orbit_sum(mono(3, 3)), 1),
        ("orbit(x^4 y^2), t=1", orbit_sum(mono(4, 2)), 1),
        ("orbit(x^5 y^4), t=3", orbit_sum(mono(5, 4)), 3),
        ("orbit(x^6 y^4), t=4", orbit_sum(mono(6, 4)), 4),
        ("orbit(x^8 y^4) + 3 orbit(x^6y^6), t=4", padd(orbit_sum(mono(8, 4)), pscale(orbit_sum(mono(6, 6)), Q(3))), 4),
        ("orbit(x^7 y^6), t=5", orbit_sum(mono(7, 6)), 5),
    ]
    ok = True
    for name, p, t in cases:
        a, b = I_t(p, t)
        exact = mp.mpf(a.numerator) / a.denominator + mp.mpf(b.numerator) / b.denominator * G
        num = I_numeric(p, t)
        err = abs(exact - num) / max(abs(num), mp.mpf('1e-6'))
        flag = "ok " if err < mp.mpf('1e-12') else "BAD"
        ok = ok and flag == "ok "
        print(f"{flag} {name:48s} a={a} b={b} exact={mp.nstr(exact,15)} quad={mp.nstr(num,15)} rel={mp.nstr(err,3)}")
    print("ALL OK" if ok else "FAILURES")
    return ok

# ---------------------------------------------------------------- the search
def lll_reduce(Qm, delta=0.99):
    """LLL on the lattice Z^n with quadratic form Qm (positive definite, float).  Returns the
    unimodular transform U (rows = reduced basis vectors in coefficient coordinates)."""
    import numpy as np
    n = Qm.shape[0]
    R = np.linalg.cholesky(Qm).T          # Qm = R^T R ; lattice basis = columns of R
    Bm = R.copy()                          # columns are basis vectors
    U = np.eye(n, dtype=np.int64)
    def gso(Bm):
        Bs = np.zeros_like(Bm); mu = np.zeros((n, n))
        for i in range(n):
            v = Bm[:, i].copy()
            for j in range(i):
                mu[i, j] = Bm[:, i] @ Bs[:, j] / (Bs[:, j] @ Bs[:, j])
                v -= mu[i, j] * Bs[:, j]
            Bs[:, i] = v
        return Bs, mu
    Bs, mu = gso(Bm)
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k, j])
            if q != 0:
                Bm[:, k] -= q * Bm[:, j]; U[:, k] -= q * U[:, j]
                Bs, mu = gso(Bm)
        if Bs[:, k] @ Bs[:, k] >= (delta - mu[k, k - 1] ** 2) * (Bs[:, k - 1] @ Bs[:, k - 1]):
            k += 1
        else:
            Bm[:, [k, k - 1]] = Bm[:, [k - 1, k]]; U[:, [k, k - 1]] = U[:, [k - 1, k]]
            Bs, mu = gso(Bm)
            k = max(k - 1, 1)
    return U.T  # rows

def search(N, t, verbose=False):
    """Degree-N positive forms F = orbit-sum(h^2), deg h = N/2, x^c y^c | h with c = ceil(t/2)."""
    import numpy as np, mpmath as mp
    mp.mp.dps = 50
    G = mp.catalan
    c = (t + 1) // 2
    d = N // 2
    basis = [(a, b) for a in range(c, d + 1) for b in range(c, d + 1 - a + c) if a + b <= d]
    basis = [(a, b) for (a, b) in basis if a >= c and b >= c]
    n = len(basis)
    if n == 0:
        return None
    # exact Gram: Q_ij = I(orbit_sum(m_i m_j), t) = A_ij + B_ij G
    A = [[None] * n for _ in range(n)]; Bq = [[None] * n for _ in range(n)]
    cache = {}
    for i in range(n):
        for j in range(i, n):
            key = (basis[i][0] + basis[j][0], basis[i][1] + basis[j][1])
            if key not in cache:
                cache[key] = I_t(orbit_sum({key: Q(1)}), t)
            A[i][j] = A[j][i] = cache[key][0]; Bq[i][j] = Bq[j][i] = cache[key][1]
    Qf = np.array([[float(A[i][j]) + float(Bq[i][j]) * float(G) for j in range(n)] for i in range(n)])
    # scale for conditioning
    s = np.sqrt(np.diag(Qf)); Qs = Qf / np.outer(s, s)
    # note: lattice is Z^n in ORIGINAL coordinates; conditioning by diagonal scaling changes the
    # lattice, so LLL on Qf directly (float64 is enough for guidance; results are re-scored exactly)
    try:
        U = lll_reduce(Qf)
    except np.linalg.LinAlgError:
        return None
    best = None
    for row in U:
        cvec = [int(v) for v in row]
        if all(v == 0 for v in cvec):
            continue
        a = sum(Q(cvec[i]) * Q(cvec[j]) * A[i][j] for i in range(n) for j in range(n) if cvec[i] and cvec[j])
        b = sum(Q(cvec[i]) * Q(cvec[j]) * Bq[i][j] for i in range(n) for j in range(n) if cvec[i] and cvec[j])
        D = lcm(a.denominator, b.denominator)
        val = mp.mpf(a.numerator) / a.denominator + mp.mpf(b.numerator) / b.denominator * G
        if val <= 0:
            continue  # cannot happen for a genuine positive form; guard against float LLL junk
        score = float(mp.log10(val)) + log10(D)
        if best is None or score < best[0]:
            best = (score, float(mp.log10(val)), log10(D), D, a, b, cvec)
    score, lv, lD, D, a, b, cvec = best
    # uniform-bound reference (t=0 only): 2^{N+2} L_N L_{N/2}
    print(f"N={N:3d} t={t:2d} dim={n:3d} | log10 I={lv:8.3f}  log10 D={lD:7.3f}  => log10(D*I)={score:8.3f}"
          f"   b={b if len(str(b)) < 30 else '…'}  |c|max={max(abs(v) for v in cvec)}")
    return best

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if cmd == "validate":
        sys.exit(0 if validate() else 1)
    elif cmd == "scan":
        Nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 16
        tmax = int(sys.argv[3]) if len(sys.argv) > 3 else 6
        for N in range(2, Nmax + 1, 2):
            for t in range(0, min(tmax, N // 2) + 1):
                try:
                    search(N, t)
                except AssertionError as e:
                    print(f"N={N} t={t}: skipped ({e})")
