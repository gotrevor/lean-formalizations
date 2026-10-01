#!/usr/bin/env -S uv run --quiet --with sympy --with numpy python3
"""Probe for PROBE-MILLS-RESIDUAL.md: the six residual mod-3 classes of the Mills problem.

Setting: f monic integer cubic, beta a root, C its companion matrix, T_j = Tr beta^(3^j) = tr C^(3^j),
D = disc f.

Claims checked:
  kron-control  KRONECKER LEMMA.  If p = T_j is prime, p = 2 (mod 3), p does not divide D*N(beta),
                and f splits completely mod p, then p | T_(j+J) with J = ord_L(3), where L is the
                lcm of the orders of the root ratios r_i/r_1 in F_p^*.  Checked by iterating
                M -> M^3 mod p J times (independent of the root computation).  Control that fails:
                the same prediction for p = 1 (mod 3) split primes, where the ratio orders carry
                3-parts and the prediction is not available.
  filter        The resulting local filter on f.  In the classes with Tr beta = 2 (mod 3)
                (tau = -1), an eventually-prime trace sequence forces (D / T_j) = -1 for all large
                j.  T_j mod |D| is eventually periodic, so this is a finite check on f.  Reports how
                much it removes beyond small-prime covering.
  saito         Totally real cubic Pisot numbers satisfying Saito's (1.3), in the six classes, that
                survive EVERY local filter we have (covering q <= 31, Kronecker / cyclic, prime
                T_0 and T_1 with the exact projective 3-order condition).  Then the one Mills-only
                condition (least-ness: no prime in (T_0^3, T_1)) is tested on them.

  tau-minus     Exhaustive census of the three tau = -1 classes in a coefficient box: covering q <= 31,
                then Kronecker, then the first covering prime beyond 31 for any survivor.

Usage: mills-residual-probe.py {kron-control|filter|saito|tau-minus|all}
"""
import sys
from math import gcd, isqrt, lcm

import numpy as np
from sympy import Poly, isprime, jacobi_symbol, n_order, nextprime, symbols, factor_list

X = symbols("x")

# Six residual classes mod 3, as (c2, c1, c0) of x^3 + c2 x^2 + c1 x + c0, with tau.
RESIDUAL = {
    (2, 2, 1): ("(x-1)^2(x+1)", 1),
    (1, 2, 2): ("(x+1)^2(x-1)", -1),
    (2, 0, 0): ("x^2(x-1)", 1),
    (1, 0, 0): ("x^2(x+1)", -1),
    (2, 1, 2): ("(x-1)(x^2+1)", 1),
    (1, 1, 1): ("(x+1)(x^2+1)", -1),
}


def cls(c):
    return RESIDUAL.get(tuple(x % 3 for x in c))


def comp(c):
    c2, c1, c0 = c
    return ((0, 0, -c0), (1, 0, -c1), (0, 1, -c2))


def mul(A, B, n):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) % n for j in range(3)) for i in range(3))


def cube(A, n):
    return mul(mul(A, A, n), A, n)


def tr(M):
    return M[0][0] + M[1][1] + M[2][2]


def disc(c):
    a, b, cc = c  # x^3 + a x^2 + b x + cc
    return a * a * b * b - 4 * b**3 - 4 * a**3 * cc - 27 * cc * cc + 18 * a * b * cc


def traces_exact(c, J):
    """T_0..T_J exactly via Newton recurrence on power sums is too slow for 3^j; use the
    composition (t, b, e) -> (t^3 - 3bt + 3e, b^3 - 3etb + 3e^2, e^3)."""
    c2, c1, c0 = c
    t, b, e = -c2, c1, -c0
    out = [t]
    for _ in range(J):
        t, b, e = t**3 - 3 * b * t + 3 * e, b**3 - 3 * e * t * b + 3 * e * e, e**3
        out.append(t)
    return out


def trace_cycle(c, n, cap=20000):
    """Eventual cycle of T_j mod n (j >= 0), as a list of residues; None if not closed by cap."""
    M = tuple(tuple(x % n for x in r) for r in comp(c))
    seen, states = {}, []
    for j in range(cap):
        if M in seen:
            return [tr(S) % n for S in states[seen[M]:]]
        seen[M] = j
        states.append(M)
        M = cube(M, n)
    return None


def kron(D, t, n):
    """Kronecker (D / p) for primes p = t (mod n), n = |D|.  0 if every such p shares a factor
    with D (then no such p exists) or if t is even with n even."""
    if gcd(t, n) != 1:
        return 0
    tt = t if t % 2 == 1 else t + n
    if tt % 2 == 0:
        return 0
    return jacobi_symbol(D % tt, tt)


def roots_mod(c, p):
    _, facs = factor_list(Poly(X**3 + c[0] * X**2 + c[1] * X + c[2], X, modulus=p))
    rts = []
    for g, m in facs:
        if g.degree() == 1:
            co = g.all_coeffs()
            rts += [(-co[1] * pow(co[0], -1, p)) % p] * m
    degs = sorted(g.degree() for g, m in facs for _ in range(m))
    return rts, degs


# ---------------------------------------------------------------------------------------------
def kron_control():
    hit = miss = 0
    ctrl_tot = ctrl_pred_ok = 0
    shown = 0
    for c2 in range(-12, 13):
        for c1 in range(-12, 13):
            for c0 in range(-6, 7):
                c = (c2, c1, c0)
                if c0 == 0:
                    continue
                D = disc(c)
                if D == 0:
                    continue
                T = traces_exact(c, 2)
                for j in (1, 2):
                    p = T[j]
                    if p < 5 or p > 10**7 or not isprime(p) or D % p == 0 or c0 % p == 0:
                        continue
                    rts, degs = roots_mod(c, p)
                    if degs != [1, 1, 1]:
                        continue
                    L = lcm(*(n_order(r * pow(rts[0], -1, p) % p, p) for r in rts[1:]))
                    if p % 3 == 2:
                        J = n_order(3, L) if L > 1 else 1
                        M = tuple(tuple(x % p for x in r) for r in comp(c))
                        for _ in range(j + J):
                            M = cube(M, p)
                        if tr(M) % p == 0:
                            hit += 1
                            if shown < 3:
                                print(f"  f=x^3{c2:+}x^2{c1:+}x{c0:+}  T_{j}={p} (=2 mod 3, split)  "
                                      f"J={J}  T_(j+J) = 0 mod p  (D/p)={jacobi_symbol(D % p, p)}")
                                shown += 1
                        else:
                            miss += 1
                    else:
                        # control: p = 1 mod 3 split.  Prediction exists only if 3 does not
                        # divide L after removing the 3^j already applied.
                        ctrl_tot += 1
                        v = 0
                        LL = L
                        while LL % 3 == 0:
                            LL //= 3
                            v += 1
                        if v <= j:
                            ctrl_pred_ok += 1
    print(f"kron-control: p=2 mod 3 split prime traces: {hit} confirmed p | T_(j+J), {miss} failed")
    print(f"  control p=1 mod 3 split prime traces: {ctrl_tot}; of these the 3-part of L is <= 3^j "
          f"(recurrence predicted) in {ctrl_pred_ok}, and absent (no prediction) in {ctrl_tot - ctrl_pred_ok}")


# ---------------------------------------------------------------------------------------------
COVER_QS = (2, 5, 7, 11, 13, 17, 19, 23, 29, 31)


def covered(c, qs=COVER_QS):
    for q in qs:
        cyc = trace_cycle(c, q)
        if cyc is not None and 0 in cyc:
            return q
    return None


def kron_killed(c, pre=60, cap=20000):
    """For tau = -1 classes.  Returns 'cyclic', 'kron', 'ok' or 'undetermined'.
    States M^(3^j) mod |D| with j >= pre lie on the cycle (the preperiod is at most
    v_3 of the unit-group exponent, below 60 for |D| < 10^9), so one bad value there kills f."""
    D = disc(c)
    if isqrt(D) ** 2 == D:
        return "cyclic"
    n = abs(D)
    M = tuple(tuple(x % n for x in r) for r in comp(c))
    seen = {}
    for j in range(cap):
        if j >= pre:
            if kron(D, tr(M) % n, n) != -1:
                return "kron"
            if M in seen:
                return "ok"
            seen[M] = j
        M = cube(M, n)
    return "undetermined"


def cyclic_split_killed(c):
    """For tau = +1 classes with cyclic K: every large T_j must split completely."""
    D = disc(c)
    F = isqrt(D)
    cyc = trace_cycle(c, F)
    if cyc is None:
        return "undetermined"
    for t in set(cyc):
        if gcd(t, F) != 1:
            return "kron"
        p = t if t > 1 else t + F
        while not isprime(p) or D % p == 0:
            p += F
        _, degs = roots_mod(c, p)
        if degs != [1, 1, 1]:
            return "kron"
    return "ok"


def irreducible(c):
    c2, c1, c0 = c
    for r in range(-abs(c0), abs(c0) + 1):
        if r != 0 and c0 % r == 0 and r**3 + c2 * r * r + c1 * r + c0 == 0:
            return False
    return True


def filt():
    """Kronecker / cyclic filter measured on its own and on the covering (q <= 13) survivors."""
    stats = {}
    for c2 in range(-30, 31):
        for c1 in range(-30, 31):
            for c0 in range(-10, 11):
                c = (c2, c1, c0)
                k = cls(c)
                if k is None or c0 == 0 or not irreducible(c):
                    continue
                D = disc(c)
                if D <= 0:
                    continue
                name, tau = k
                s = stats.setdefault(name, {"n": 0, "kron": 0, "und": 0, "cov13": 0, "cov13+kron": 0})
                s["n"] += 1
                if tau == -1:
                    r = kron_killed(c)
                elif isqrt(D) ** 2 == D:
                    r = cyclic_split_killed(c)
                else:
                    r = "ok"
                killed = r in ("kron", "cyclic")
                s["kron"] += killed
                s["und"] += r == "undetermined"
                if not covered(c, (2, 5, 7, 11, 13)):
                    s["cov13"] += 1
                    s["cov13+kron"] += not killed
    print("filter: totally real irreducible cubics, |c2|,|c1| <= 30, |c0| <= 10, by residual class")
    print(f"  {'class':16} {'n':>6} {'kron kills':>10} {'undet':>6} {'cover<=13 surv':>15} {'then kron surv':>15}")
    for name, s in stats.items():
        print(f"  {name:16} {s['n']:6} {s['kron']:10} {s['und']:6} {s['cov13']:15} {s['cov13+kron']:15}")


# ---------------------------------------------------------------------------------------------
def proj3order(c, p):
    """v_3 of the order of beta in (F_p[x]/f)^* / F_p^*, for p not dividing D*N."""
    _, degs = roots_mod(c, p)
    n = 1
    for d in degs:
        n *= p**d - 1
    v = 0
    m = n
    while m % 3 == 0:
        m //= 3
        v += 1
    c2, c1, c0 = c

    def pmul(a, b):
        r = [0] * 5
        for i in range(3):
            for k in range(3):
                r[i + k] += a[i] * b[k]
        for d in (4, 3):  # x^3 = -c2 x^2 - c1 x - c0
            co = r[d]
            r[d] = 0
            r[d - 1] -= c2 * co
            r[d - 2] -= c1 * co
            r[d - 3] -= c0 * co
        return [x % p for x in r[:3]]

    def ppow(a, e):
        R = [1, 0, 0]
        while e:
            if e & 1:
                R = pmul(R, a)
            a = pmul(a, a)
            e >>= 1
        return R

    h = ppow([0, 1, 0], m)
    i = 0
    while h[1] or h[2]:
        h = ppow(h, 3)
        i += 1
    return i, degs


_COVER_TABLE = {}


def cover_table(q):
    """Set of (c2, c1, c0) mod q whose trace orbit mod q has 0 in its cycle."""
    if q not in _COVER_TABLE:
        import itertools
        _COVER_TABLE[q] = {c for c in itertools.product(range(q), repeat=3) if 0 in trace_cycle(c, q)}
    return _COVER_TABLE[q]


def covered_fast(c, qs=COVER_QS):
    for q in qs:
        if tuple(x % q for x in c) in cover_table(q):
            return q
    return None


def saito_family(B):
    """Totally real cubic Pisot beta < ~B with Saito's (1.3), in the six classes (batched)."""
    out = []
    for c2 in range(-B, -2):
        beta = -c2
        nmax = int(beta ** 0.15)
        lim = int(2 * (beta + 2) ** (23 / 40)) + 3
        c1s = np.arange(-lim, 4)
        for c0 in [n for n in range(-nmax, nmax + 1) if n != 0]:
            k = len(c1s)
            M = np.zeros((k, 3, 3))
            M[:, 1, 0] = 1
            M[:, 2, 1] = 1
            M[:, 0, 2] = -c0
            M[:, 1, 2] = -c1s
            M[:, 2, 2] = -c2
            ev = np.linalg.eigvals(M)
            real = np.all(np.abs(ev.imag) < 1e-9, axis=1)
            for i in np.nonzero(real)[0]:
                r = sorted(ev[i].real, key=lambda z: -abs(z))
                b1, b2, b3 = r
                if not (b1 > 1 and abs(b2) < 1 and b2 < 0):
                    continue
                if not (abs(b3) < -b2 <= min(abs(b3) ** (17 / 23), b1 ** (-17 / 40))):
                    continue
                c = (c2, int(c1s[i]), c0)
                k3 = cls(c)
                if k3 is None or not irreducible(c):
                    continue
                out.append((c, k3, b1, b2, b3))
    return out


def saito(B=6000):
    rows = saito_family(B)
    print(f"saito: {len(rows)} totally real cubic Pisot numbers beta < ~{B} with (1.3) in the six classes")
    per = {}
    surv = []
    for c, (name, tau), b1, b2, b3 in rows:
        s = per.setdefault(name, [0, 0, 0])
        s[0] += 1
        if covered_fast(c):
            continue
        s[1] += 1
        D = disc(c)
        if tau == -1:
            res = kron_killed(c)
        elif isqrt(D) ** 2 == D:
            res = cyclic_split_killed(c)
        else:
            res = "ok"
        if res in ("kron", "cyclic"):
            continue
        s[2] += 1
        surv.append((c, name, res, b2 + b3))
    print(f"  {'class':16} {'(1.3)':>7} {'cover<=31 surv':>15} {'then kron/cyclic surv':>22}")
    for name, (a, b, cc) in per.items():
        print(f"  {name:16} {a:7} {b:15} {cc:22}")
    print("  local survivors (first 12), and the Mills-only test: is (T0^3, T1) prime-free?")
    held = 0
    for c, name, res, s0 in surv:
        T0, T1 = traces_exact(c, 1)
        q = nextprime(T0**3)
        held += q >= T1
    for c, name, res, s0 in surv[:12]:
        T0, T1 = traces_exact(c, 1)
        q = nextprime(T0**3)
        print(f"    x^3{c[0]:+}x^2{c[1]:+}x{c[2]:+}  [{name}{'' if res == 'ok' else ', ' + res}]  "
              f"T0={T0}{'*' if isprime(T0) else ''}  gap Mills needs prime-free: {T1 - T0**3}, "
              f"first prime after T0^3 at +{q - T0**3}")
    print(f"  prime-free gap (least-ness) holds for {held} of {len(surv)} local survivors")
    fq = [first_cover_prime(c) for c, *_ in surv]
    from collections import Counter
    print(f"  first covering prime in 37..3000 for the local survivors: {sorted(Counter(fq).items(), key=str)}")


def first_cover_prime(c, lo=37, hi=3000):
    from sympy import primerange
    for q in primerange(lo, hi):
        cyc = trace_cycle(c, q, cap=300000)
        if cyc is not None and 0 in cyc:
            return q
    return None


def tau_minus():
    """Exhaustive: tau = -1 classes, c2 = 1 mod 3 in [-299, 301], |c1| <= 300, 0 < |c0| <= 30."""
    tabs = [(q, cover_table(q)) for q in COVER_QS]
    n = cs = 0
    ok, und = [], []
    for c2 in range(-299, 302, 3):
        for c1 in range(-300, 301):
            for c0 in range(-30, 31):
                c = (c2, c1, c0)
                if c0 == 0 or cls(c) is None:
                    continue
                n += 1
                if any((c2 % q, c1 % q, c0 % q) in t for q, t in tabs):
                    continue
                if disc(c) <= 0 or not irreducible(c):
                    continue
                cs += 1
                r = kron_killed(c)
                if r == "ok":
                    ok.append(c)
                elif r == "undetermined":
                    und.append(c)
    print(f"tau-minus: {n} cubics in the three tau = -1 classes; {cs} totally real irreducible survive "
          f"covering q <= 31; {len(ok)} survive Kronecker ({len(und)} undetermined)")
    for c in ok:
        print(f"  survivor x^3{c[0]:+}x^2{c[1]:+}x{c[2]:+}: first covering prime {first_cover_prime(c)}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd in ("kron-control", "all"):
        kron_control()
    if cmd in ("filter", "all"):
        filt()
    if cmd in ("saito", "all"):
        saito()
    if cmd in ("tau-minus", "all"):
        tau_minus()
