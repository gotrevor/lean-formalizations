#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Saito Problem 1.7 probe (2026-09-30): R(n) = c^n + s (non-reversible ILRS, R(n+1) = cR(n) - (c-1)s).
For each Pisot alpha (degree 2 and 3), the floor is floor(alpha^N) = tr C^N + eps_N, eps_N in {0,-1}.
Survivor test (prime-as-modulus filter): for every limit point lambda_r of tr C^(R(n)) (c-adic, along
residue classes of n), lambda_r + eps must lie in {+1,-1} for eps in {0,-1}, i.e. lambda_r in {-2,-1,0,1,2}
modulo c^(K/2).  Reports alpha with survivors, per shift s.  Known-answer control: s = 0 at c = 3 must
reproduce the Mills residual classes (survivors exist)."""
import itertools, sys
import numpy as np

def is_pisot(coeffs):  # monic x^d + coeffs[0] x^(d-1) + ... ; returns dominant root or None
    r = np.roots([1] + list(coeffs))
    mags = sorted(abs(r))
    if mags[-1] <= 1 + 1e-9 or mags[-2] >= 1 - 1e-9: return None
    big = max(r, key=abs)
    if abs(big.imag) > 1e-9 or big.real <= 1: return None
    if abs(coeffs[-1]) == 0: return None
    return big.real

def companion(coeffs):  # x^d + a1 x^(d-1) + ... + ad
    d = len(coeffs)
    C = [[0]*d for _ in range(d)]
    for j in range(d): C[0][j] = -coeffs[j]
    for i in range(1, d): C[i][i-1] = 1
    return C

def mm(A, B, m):
    d = len(A); return [[sum(A[i][k]*B[k][j] for k in range(d)) % m for j in range(d)] for i in range(d)]
def mp(A, e, m):
    d = len(A); R = [[int(i == j) for j in range(d)] for i in range(d)]; A = [[x % m for x in r] for r in A]
    while e:
        if e & 1: R = mm(R, A, m)
        A = mm(A, A, m); e >>= 1
    return R

def survivors(C, c, s, K=None):
    K = K or KPREC
    m = c**K; d = len(C)
    period = 1
    # period of limit points divides lcm(1..d) (Frobenius orbit lengths); test n over a window
    tgt = c**(K//2)
    ok = True
    for n in range(2*K, 2*K + 6):
        t = sum(mp(C, c**n + s, m)[i][i] for i in range(d)) % m
        if not any((t + eps) % tgt in (1, tgt - 1) for eps in (0, -1)): ok = False; break
    return ok

c = int(sys.argv[1]) if len(sys.argv) > 1 else 3
KPREC = int(sys.argv[2]) if len(sys.argv) > 2 else 8
shifts = range(0, 7)
cnt = {s: 0 for s in shifts}; tot = 0; examples = {s: [] for s in shifts}
for a1, a2, a3 in itertools.product(range(-6, 7), repeat=3):
    co = (a1, a2, a3)
    if a3 % c == 0: continue           # p does not divide det: need c-adic unit det for Teichmuller picture
    al = is_pisot(co)
    if al is None: continue
    tot += 1
    C = companion(co)
    for s in shifts:
        if survivors(C, c, s):
            cnt[s] += 1
            if len(examples[s]) < 3: examples[s].append(co)
for a1, a2 in itertools.product(range(-8, 9), repeat=2):
    co = (a1, a2)
    if a2 % c == 0: continue
    if is_pisot(co) is None: continue
    tot += 1
    C = companion(co)
    for s in shifts:
        if survivors(C, c, s):
            cnt[s] += 1
            if len(examples[s]) < 3: examples[s].append(co)
print(f"c={c}, precision c^{KPREC//2}: {tot} Pisot alphas (deg 2,3; det prime to c).  alphas with survivors, by shift s:")
for s in shifts: print(f"  s={s}: {cnt[s]}  e.g. {examples[s]}")
