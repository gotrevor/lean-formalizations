#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Theorem E, exception E1 (PROOF-THEOREM-E.md): the conductor-13 cyclic cubic field K contributes nothing.

In K ⊂ ℚ(ζ₁₃) the prime 3 is inert, and Frobenius at 3 is τ₃ : ζ ↦ ζ³, generating D = {1, 3, 9} ⊂ (ℤ/13)^×.
The Teichmüller roots are ζ_k = τ_(3^k)(ζ₀), ζ₀ = ±ζ^b.  Galois rigidity reduces to: Tr_D(ζ₀′ w) ∈ ℚ for
w = α^s ∈ K (any shift s).  This script checks that for every b the ℚ-linear map
  K → ℚ(ζ₁₃)/ℚ,  w ↦ Tr_D(ζ^b w)
is injective (rank 3 on the basis of cubic Gaussian periods η_j = Σ_(h ∈ H) ζ^(3^j h), H = {1,5,8,12}).
Injective ⇒ w = 0, impossible for w = α^s.  Hence E1 is empty.  Exits nonzero if any rank < 3."""
import sys
from sympy import Matrix
p = 13
def mul(a, b):
    r = [0]*p
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: r[(i+j) % p] += x*y
    return r
def tau(a, d):
    r = [0]*p
    for i, x in enumerate(a): r[(i*d) % p] += x
    return r
def add(a, b): return [x+y for x, y in zip(a, b)]
def zpow(m): r = [0]*p; r[m % p] = 1; return r
H, D = [1, 5, 8, 12], [1, 3, 9]
eta = [[0]*p for _ in range(3)]
for j in range(3):
    for h in H: eta[j] = add(eta[j], zpow(pow(3, j, p)*h))
def nonrational_part(a):          # coordinates in basis ζ¹..ζ¹² ; rational iff all equal
    v = [a[m] - a[0] for m in range(1, p)]
    return [v[i] - v[0] for i in range(1, 12)]
bad = []
for b in range(1, p):
    cols = []
    for j in range(3):
        phi = [0]*p
        for d in D: phi = add(phi, mul(tau(zpow(b), d), tau(eta[j], d)))
        cols.append(nonrational_part(phi))
    rk = Matrix(cols).T.rank()
    print(f"b={b:2d}: rank {rk}")
    if rk < 3: bad.append(b)
print("E1 EMPTY (all ranks 3)" if not bad else f"FAIL at b={bad}")
sys.exit(1 if bad else 0)
