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

  pair-control  PAIRED-ROOT LEMMA (§7).  At a (1)(2) prime T_j with v_3(T_j - 1) = j + 1 and N(beta) a
                cube, the projective 3-order is <= j and p | T_(j+J); checked by a direct matrix power.
                Control: s >= j + 2, no prediction.
  tau-plus      tau = +1 S3 census: the 3-adic rate c_j, and the paired-root Jacobi filter on unit
                cubics with c_j = 1.
  hard-core     [box c0max J cmin]: depth of the root ratios at prime T_j against random primes
                with the same v_3(p - 1) and splitting type.  Is anything forced?

Usage: mills-residual-probe.py {kron-control|filter|saito|tau-minus|pair-control|tau-plus|hard-core|all}
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


# ---------------------------------------------------------------------------------------------
def v3(n):
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v


def hard_core(box=40, c0max=4, J=3, cmin=1, seed=1):
    """The hard core: tau = +1 classes with K an S3 field.  At p = T_j prime the recurrence
    p | T_(j+k) is excluded iff v_3(projective order of beta mod p) > j (PROBE §3).  With
    s = v_3(p - 1) and v that 3-adic valuation, record d = s - v (the depth to which the root
    ratios are 3-power residues; split + s = j + 1 means d = 0 iff the cube classes of the roots
    are not all equal).  Is d at the Mills-like primes p = T_j distributed like d at random
    primes q with the same s and the same splitting type in K (the control)?"""
    import random
    from collections import Counter
    rng = random.Random(seed)
    obs, ctl = Counter(), Counter()
    corr = Counter()
    n_f = 0
    for c2 in range(-box, box + 1):
        for c1 in range(-box, box + 1):
            for c0 in range(-c0max, c0max + 1):
                c = (c2, c1, c0)
                k = cls(c)
                if k is None or k[1] != 1 or c0 == 0 or not irreducible(c):
                    continue
                D = disc(c)
                if D <= 0 or isqrt(D) ** 2 == D:
                    continue
                pat = c_of(c)
                if pat is None or max(pat) < cmin:
                    continue
                n_f += 1
                T = traces_exact(c, J)
                for j in range(1, J + 1):
                    p = T[j]
                    if p < 10**4 or not isprime(p) or D % p == 0 or c0 % p == 0:
                        continue
                    if pat[j % 2] < cmin:
                        continue
                    s = v3(p - 1)
                    v, degs = proj3order(c, p)
                    if degs not in ([1, 1, 1], [1, 2]):
                        continue
                    typ = "split" if degs == [1, 1, 1] else "(1)(2)"
                    obs[(typ, s - j, min(s - v, 3), v > j)] += 1
                    corr[(typ, s - j, ((p - 1) // 3**s) % 3, s - v)] += 1
                    # control: random primes q with v_3(q - 1) = s, same size, same type in K
                    got = 0
                    while got < 3:
                        u = rng.randrange(max(1, p // 3**s // 2), p // 3**s + 2)
                        if u % 3 == 0:
                            continue
                        q = 1 + 3**s * u
                        if not isprime(q) or D % q == 0 or c0 % q == 0:
                            continue
                        vq, dq = proj3order(c, q)
                        if dq != degs:
                            continue
                        ctl[(typ, s - j, min(s - vq, 3), vq > j)] += 1
                        got += 1
    print(f"hard-core: {n_f} S3 cubics in the tau = +1 classes with 3-adic rate c_j >= {cmin} (at the j used), "
          f"|c2|,|c1| <= {box}, |c0| <= {c0max}; "
          f"primes p = T_j (1 <= j <= {J}, p > 10^4) of type split / (1)(2)")
    print(f"  {'type':7} {'c=s-j':>5} {'d=s-v':>6} {'v>j':>5} {'obs':>6} {'ctl/3':>7}")
    keys = sorted(set(obs) | set(ctl), key=str)
    for key in keys:
        print(f"  {key[0]:7} {key[1]:5} {key[2]:6} {str(key[3]):>5} {obs[key]:6} {ctl[key] / 3:7.1f}")
    for typ in ("split", "(1)(2)"):
        o = sum(n for kk, n in obs.items() if kk[0] == typ)
        ob = sum(n for kk, n in obs.items() if kk[0] == typ and not kk[3])
        cc = sum(n for kk, n in ctl.items() if kk[0] == typ)
        cb = sum(n for kk, n in ctl.items() if kk[0] == typ and not kk[3])
        print(f"  {typ}: recurrence (v <= j) at p = T_j in {ob}/{o}; control {cb}/{cc}")
    print("  correlation of d with (p-1)/3^s mod 3 at p = T_j (type, c, residue, d): count")
    for key in sorted(corr, key=str):
        print(f"    {key}: {corr[key]}")


def c_of(c, K=60, j0=26, j1=33):
    """The 3-adic rate c_j = v_3(T_j - 1) - j for large j, as (c at even j, c at odd j).  In
    (x-1)(x^2+1) with x^2+1 inert at 3 it alternates (the Teichmuller roots +-i swap under
    cubing), elsewhere it is constant.  None if not yet periodic within 3^K."""
    n = 3**K
    M = tuple(tuple(x % n for x in r) for r in comp(c))
    vals = {}
    for j in range(j1 + 1):
        if j >= j0:
            t = (tr(M) - 1) % n
            vals.setdefault(j % 2, set()).add((v3(t) if t else K) - j)
        M = cube(M, n)
    if any(len(v) != 1 for v in vals.values()):
        return None
    pat = (min(vals[0]), min(vals[1]))
    return pat if max(pat) + j1 < K else None


def pair_control(box=12, c0s=(-1, 1)):
    """PAIRED-ROOT LEMMA.  A Frobenius-conjugate pair of roots in F_(p^2) has one cube class
    (rho^p = rho * rho^(p-1) and p = 1 mod 3), so if N(beta) is a cube mod p the third root
    shares it too.  Hence at p = T_j of type (1)(2) with v_3(p - 1) = j + 1, the projective order
    has v_3 <= j and p | T_(j+J) for some J >= 1.  Checked by iterating M -> M^3 mod p (an
    independent route).  Control: (1)(2) primes T_j with v_3(p - 1) >= j + 2, where the lemma
    makes no prediction."""
    hit = miss = 0
    ctl = ctl_rec = 0
    for c2 in range(-box, box + 1):
        for c1 in range(-box, box + 1):
            for c0 in c0s:
                c = (c2, c1, c0)
                D = disc(c)
                if not irreducible(c) or D == 0 or isqrt(abs(D)) ** 2 == D:
                    continue
                T = traces_exact(c, 2)
                for j in (1, 2):
                    p = T[j]
                    if p < 5 or p > 10**7 or p % 3 != 1 or not isprime(p) or D % p == 0:
                        continue
                    v, degs = proj3order(c, p)
                    if degs != [1, 2]:
                        continue
                    s = v3(p - 1)
                    if s == j + 1:
                        # predicted: v <= j, so x = beta^(3^j) has projective order L prime to 3;
                        # verify independently: T_(j+J) = 0 mod p with J = ord_L(3), via M^(3^(j+J))
                        # with the exponent reduced mod p^2 - 1 (M is semisimple mod p).
                        L = proj_order(c, p, 3**j)
                        rec = False
                        if L % 3:
                            J = n_order(3, L) if L > 1 else 1
                            e = pow(3, j + J, p * p - 1)
                            rec = tr(mat_pow(comp(c), e, p)) % p == 0
                        hit += rec and v <= j
                        miss += not (rec and v <= j)
                    elif s >= j + 2:
                        ctl += 1
                        ctl_rec += v <= j
    print(f"pair-control: (1)(2) prime traces T_j = 1 mod 3 with v_3(T_j - 1) = j + 1, unit beta: "
          f"{hit} have v <= j and p | T_(j+J) (checked by matrix power), {miss} do not")
    print(f"  control v_3(T_j - 1) >= j + 2: {ctl} primes; v <= j (recurrence) in {ctl_rec}, "
          f"no prediction in {ctl - ctl_rec}")


def mat_pow(A, e, n):
    R = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    A = tuple(tuple(x % n for x in r) for r in A)
    while e:
        if e & 1:
            R = mul(R, A, n)
        A = mul(A, A, n)
        e >>= 1
    return R


def proj_order(c, p, k):
    """Order of beta^k in (F_p[x]/f)^* / F_p^*, for (1)(2) primes (the group has exponent p^2 - 1)."""
    from sympy import factorint
    def scalar(M):
        return M[0][1] == M[0][2] == M[1][0] == M[1][2] == M[2][0] == M[2][1] == 0 and M[0][0] == M[1][1] == M[2][2]
    X0 = mat_pow(comp(c), k, p)
    L = p * p - 1
    for q, e in factorint(L).items():
        for _ in range(e):
            if scalar(mat_pow(X0, L // q, p)):
                L //= q
            else:
                break
    return L



def plus_killed(c, par, pre=60, cap=20000):
    """tau = +1, S3, unit beta.  At every large j with c_j = 1 (j mod 2 in par), the prime T_j
    cannot have type (1)(2) (paired-root lemma) or (3) (projective lemma), so it splits
    completely and (D / T_j) = +1.  One such cycle value of T_j mod |D| with (D/.) in {0, -1}
    kills f.  The state is (M^(3^j) mod |D|, j mod 2)."""
    D = disc(c)
    n = abs(D)
    M = tuple(tuple(x % n for x in r) for r in comp(c))
    seen = {}
    for j in range(cap):
        if j >= pre:
            if j % 2 in par and kron(D, tr(M) % n, n) != 1:
                return "kron"
            if (M, j % 2) in seen:
                return "ok"
            seen[(M, j % 2)] = j
        M = cube(M, n)
    return "undetermined"


def tau_plus(box=30, c0max=10):
    """The tau = +1 S3 census: distribution of the 3-adic rate pattern (c_even, c_odd), and the
    paired-root Jacobi filter on unit f with c_j = 1 at some parity, alone and after covering."""
    from collections import Counter
    cdist = Counter()
    unit = Counter()
    for c2 in range(-box, box + 1):
        for c1 in range(-box, box + 1):
            for c0 in range(-c0max, c0max + 1):
                c = (c2, c1, c0)
                k = cls(c)
                if k is None or k[1] != 1 or c0 == 0 or not irreducible(c):
                    continue
                D = disc(c)
                if D <= 0 or isqrt(D) ** 2 == D:
                    continue
                pat = c_of(c)
                cdist[(k[0], "c=1 some parity" if pat and 1 in pat else pat and "c>=2")] += 1
                if abs(c0) != 1:
                    continue
                par = {i for i in (0, 1) if pat and pat[i] == 1}
                key = (k[0], "c=1" if par else "c>=2")
                unit[key + ("n",)] += 1
                r = plus_killed(c, par) if par else "n/a"
                unit[key + ("kron kills",)] += r == "kron"
                unit[key + ("undetermined",)] += r == "undetermined"
                cov = covered(c, (2, 5, 7, 11, 13))
                unit[key + ("cover<=13 surv",)] += not cov
                unit[key + ("cover<=13 then kron surv",)] += not cov and r != "kron"
    print(f"tau-plus: totally real S3 cubics, tau = +1, |c2|,|c1| <= {box}, |c0| <= {c0max}")
    print("  3-adic rate pattern (None: not periodic within the window):")
    for key in sorted(cdist, key=str):
        print(f"    {key}: {cdist[key]}")
    print("  unit f (|c0| = 1): paired-root Jacobi filter")
    for key in sorted(unit, key=str):
        print(f"    {key}: {unit[key]}")

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
    if cmd == "pair-control":
        pair_control(*(int(a) for a in sys.argv[2:3]))
    if cmd == "tau-plus":
        tau_plus(*(int(a) for a in sys.argv[2:]))
    if cmd == "hard-core":
        hard_core(*(int(a) for a in sys.argv[2:]))
