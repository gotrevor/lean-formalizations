#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Probe for PROBE-MILLS-3ADIC.md.

Setting: beta is a root of a monic integer polynomial f, p_m = Tr beta^(3^m).

Claims checked:
  gauss  p_m = p_{m-1} (mod 3^m), so p_m converges 3-adically to tau.
  mech   q prime, q | p_m, q not dividing N(beta), and the 3-part of |F_{q^f}^*| is at most 3^m
         for every f <= deg f.  Then alpha = beta^(3^m) mod q has period L with 3 not dividing L,
         and q | p_{m+j} for j = ord_L(3).
  chain  the full argument on cases where p_m is PRIME: p_m | p_{m+j} for that j.
  tau    tau mod 3 classes: the argument needs tau + h not in {1, -1} (h = floor offset).

Usage: mills-3adic-probe.py {gauss|mech|tau|chain|covering|all}
"""
import sys
from math import lcm
from sympy import factorint, n_order, isprime


def matmul(A, B, q=None):
    n = len(A)
    C = [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    return [[x % q for x in r] for r in C] if q else C


def matpow(A, e, q=None):
    n = len(A)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    while e:
        if e & 1:
            R = matmul(R, A, q)
        A = matmul(A, A, q)
        e >>= 1
    return R


def comp(c):
    """Companion matrix of x^3 + c2 x^2 + c1 x + c0."""
    c2, c1, c0 = c
    return [[0, 0, -c0], [1, 0, -c1], [0, 1, -c2]]


def tr(M):
    return sum(M[i][i] for i in range(len(M)))


def v3(n):
    if n == 0:
        return 10**9
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k


I3 = [[int(i == j) for j in range(3)] for i in range(3)]


def matorder(A, q):
    N = lcm(q - 1, q * q - 1, q**3 - 1) * q  # factor q: a repeated root mod q is unipotent
    o = N
    for p, e in factorint(N).items():
        for _ in range(e):
            if matpow(A, o // p, q) == I3:
                o //= p
            else:
                break
    assert matpow(A, o, q) == I3
    return o


def small_prime_factors(n, B):
    """Prime factors 3 < r < B of n, by trial division (sympy's limit= still runs rho)."""
    out, r = [], 5
    while r < B:
        if n % r == 0 and isprime(r):
            out.append(r)
        r += 2
    return out


def p_seq(c, M):
    C = comp(c)
    out, X = [], C
    for _ in range(M + 1):
        out.append(tr(X))
        X = matpow(X, 3)
    return out


POLYS = [(-1, -1, -1), (0, -1, -1), (-3, 0, 1), (-4, 2, 1), (-5, 3, 1), (-2, -1, 1),
         (-6, 5, -1), (-4, 1, 1), (-5, 2, 1), (-7, 3, 2), (-3, -2, 3)]


def gauss():
    bad = 0
    for c in POLYS:
        ps = p_seq(c, 6)
        for m in range(1, 7):
            if (ps[m] - ps[m - 1]) % 3**m:
                bad += 1
                print("  FAIL", c, m)
    print(f"gauss: {len(POLYS)} polys x m=1..6, failures {bad}")
    return bad == 0


def mech():
    tested = hits = skipped = 0
    for c in POLYS:
        C = comp(c)
        for m in range(1, 5):
            pm = tr(matpow(C, 3**m))
            for r in small_prime_factors(abs(pm), 10**5):
                if c[2] % r == 0:
                    continue
                if max(v3(r**f - 1) for f in (1, 2, 3)) > m:
                    skipped += 1
                    continue
                A = matpow(C, 3**m, r)
                L = matorder(A, r)
                assert L % 3, (c, m, r, L)  # the lemma: 3-part is killed
                j = n_order(3, L)
                L0 = matorder([[x % r for x in row] for row in C], r)  # independent route
                ok = tr(matpow(C, pow(3, m + j, L0), r)) % r == 0
                tested += 1
                hits += ok
                if not ok:
                    print("  FAIL", c, m, r, L, j)
    print(f"mech: {tested} prime moduli with small 3-part, {hits} divide p_(m+j); "
          f"{skipped} skipped (3-part too big)")
    return tested > 0 and hits == tested


def chain():
    """Known-answer control: cases where p_m is actually prime."""
    found = 0
    for c2 in range(-9, 1):
        for c1 in range(-6, 7):
            for c0 in (-3, -2, -1, 1, 2, 3):
                c = (c2, c1, c0)
                C = comp(c)
                for m in (1, 2):
                    pm = tr(matpow(C, 3**m))
                    if pm < 10**4 or pm > 10**14 or not isprime(pm) or c0 % pm == 0:
                        continue
                    if max(v3(pm**f - 1) for f in (1, 2, 3)) > m:
                        continue
                    L = matorder(matpow(C, 3**m, pm), pm)
                    j = n_order(3, L)
                    L0 = matorder([[x % pm for x in row] for row in C], pm)
                    ok = tr(matpow(C, pow(3, m + j, L0), pm)) % pm == 0
                    print(f"  f={c} m={m} p_m={pm} prime, L 3-free, j={j}: p_m | p_(m+j) {ok}")
                    found += 1
                    if not ok:
                        return False
                    if found >= 8:
                        return True
    return found > 0


# f mod 3 whose Teichmüller root sum is ±1: roots {1,1,-1}, {-1,-1,1}, {0,0,±1}, {±1, i, -i}.
def fmod3(c):
    return tuple(x % 3 for x in c)


RESIDUAL = {
    # (x-1)^2 (x+1) = x^3 - x^2 - x + 1
    (2, 2, 1): 1,
    # (x+1)^2 (x-1) = x^3 + x^2 - x - 1
    (1, 2, 2): -1,
    # x^2 (x-1) = x^3 - x^2
    (2, 0, 0): 1,
    # x^2 (x+1) = x^3 + x^2
    (1, 0, 0): -1,
    # (x-1)(x^2+1) = x^3 - x^2 + x - 1
    (2, 1, 2): 1,
    # (x+1)(x^2+1) = x^3 + x^2 + x + 1
    (1, 1, 1): -1,
}


def tau():
    """tau = lim p_m in Z_3 is ±1 exactly when f mod 3 is in RESIDUAL (checked mod 3^7)."""
    Q, bad, n = 3**8, 0, 0
    for c2 in range(-6, 7):
        for c1 in range(-6, 7):
            for c0 in range(-6, 7):
                if c0 == 0:
                    continue
                c = (c2, c1, c0)
                t = tr(matpow(comp(c), 3**10, Q)) % 3**7
                is_pm1 = t in (1, 3**7 - 1)
                pred = fmod3(c) in RESIDUAL
                n += 1
                if is_pm1 != pred or (pred and t % 3 != RESIDUAL[fmod3(c)] % 3):
                    bad += 1
                    if bad < 5:
                        print("  FAIL", c, fmod3(c), t)
    print(f"tau: {n} cubics, tau = ±1 (mod 3^7) iff f mod 3 in the six residual classes; mismatches {bad}")
    return bad == 0


def covering(qs=(2, 5, 7, 11, 13)):
    """Fraction of monic cubics f mod q whose eventual orbit t_k = tr C^(3^k) mod q hits 0.
    Such f cannot give eventually-prime t_k (t_k -> infinity).  CRT-independent of the mod-3 class."""
    surv = 1.0
    for q in qs:
        killed = tot = 0
        for c2 in range(q):
            for c1 in range(q):
                for c0 in range(q):
                    X = [[x % q for x in r] for r in comp((c2, c1, c0))]
                    seen, seq = {}, []
                    while True:
                        key = tuple(map(tuple, X))
                        if key in seen:
                            break
                        seen[key] = len(seq)
                        seq.append(tr(X) % q)
                        X = matmul(matmul(X, X, q), X, q)
                    cyc = seq[seen[key]:]
                    tot += 1
                    killed += 0 in cyc
        surv *= 1 - killed / tot
        print(f"  q={q}: {killed}/{tot} cubics mod q killed; surviving fraction so far {surv:.3f}")
    return True


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    res = []
    if what in ("gauss", "all"):
        res.append(gauss())
    if what in ("mech", "all"):
        res.append(mech())
    if what == "covering":
        res.append(covering())
    if what in ("tau", "all"):
        res.append(tau())
    if what in ("chain", "all"):
        r = chain()
        print("chain:", "ok" if r else "FAIL")
        res.append(r)
    sys.exit(0 if all(res) else 1)
