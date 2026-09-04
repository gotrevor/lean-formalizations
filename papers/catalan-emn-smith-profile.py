#!/usr/bin/env -S uv run --quiet python3
"""Local Smith-profile proxy for the exact EMN coefficient map.

This is deliberately not called a Frobenius computation.  For the lattice of
sigma-invariant integer polynomials F of bounded degree, it computes the exact map

    F |-> (a,b),  integral F/g^(t+1) = a + b*G,

clears the least common denominator D of the whole matrix, and reports the p-adic
Smith invariants of the resulting 2-by-d integer matrix.  They determine the exact
index cost of imposing p^k divisibility on both output coordinates:

    [Z^d : {c : M c = 0 mod p^k}]
      = p^(max(0,k-alpha_1) + max(0,k-alpha_2)).

This measures the observable local saturation already present in the EMN map.  An
actual Frobenius-saturated search additionally needs a Frobenius operator and an
integral comparison theorem; this script does not pretend to supply either one.
"""

from __future__ import annotations

from fractions import Fraction
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from math import gcd, log10
from pathlib import Path
import sys


def load_emn():
    path = Path(__file__).with_name("catalan-emn-search.py")
    spec = spec_from_file_location("catalan_emn_search", path)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EMN = load_emn()


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation(value: int, prime: int) -> int:
    if value == 0:
        return 10**9
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def prime_factors(value: int) -> list[int]:
    factors = []
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            factors.append(prime)
            while value % prime == 0:
                value //= prime
        prime += 1 if prime == 2 else 2
    if value > 1:
        factors.append(value)
    return factors


def canonical(poly) -> tuple:
    return tuple(sorted(poly.items()))


def invariant_basis(max_degree: int, t: int):
    required = 2 * ((t + 1) // 2)
    seen = set()
    basis = []
    for a in range(required, max_degree + 1):
        for b in range(required, max_degree + 1 - a):
            poly = EMN.orbit_sum({(a, b): Fraction(1)})
            key = canonical(poly)
            if poly and key not in seen:
                seen.add(key)
                basis.append(poly)
    return basis


def smith_gcds(columns: list[tuple[int, int]]) -> tuple[int, int, int]:
    """Return rank, first determinantal divisor, second determinantal divisor."""
    delta1 = 0
    for x, y in columns:
        delta1 = gcd(delta1, abs(x))
        delta1 = gcd(delta1, abs(y))
    delta2 = 0
    for (x1, y1), (x2, y2) in combinations(columns, 2):
        delta2 = gcd(delta2, abs(x1 * y2 - x2 * y1))
        if delta2 == 1:
            break
    rank = 2 if delta2 else (1 if delta1 else 0)
    return rank, delta1, delta2


def profile(max_degree: int, t: int) -> None:
    basis = invariant_basis(max_degree, t)
    forms = [EMN.I_t(poly, t) for poly in basis]
    denominator = 1
    for a, b in forms:
        denominator = lcm(denominator, a.denominator)
        denominator = lcm(denominator, b.denominator)
    columns = [
        (a.numerator * (denominator // a.denominator),
         b.numerator * (denominator // b.denominator))
        for a, b in forms
    ]
    rank, delta1, delta2 = smith_gcds(columns)
    print(
        f"N={max_degree:2d} t={t:2d} dim={len(basis):3d} rank={rank} "
        f"log10D={log10(denominator):8.3f}"
    )
    if rank < 2:
        return
    total_log_index = 0.0
    for prime in prime_factors(denominator):
        d = valuation(denominator, prime)
        alpha1 = valuation(delta1, prime)
        alpha2 = valuation(delta2 // delta1, prime)
        cost = max(0, d - alpha1) + max(0, d - alpha2)
        total_log_index += cost * log10(prime)
        print(
            f"  p={prime:3d} delta={d:3d} smith=({alpha1:3d},{alpha2:3d}) "
            f"full-clear-index=p^{cost} cost/dim={cost/max(1,len(basis)):.4f}"
        )
    print(
        f"  TOTAL log10(index)={total_log_index:.3f} "
        f"index/logD={total_log_index/log10(denominator):.3f} "
        f"log10(index)/dim={total_log_index/max(1,len(basis)):.4f}"
    )


def main() -> None:
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    t = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    if len(sys.argv) > 3 and sys.argv[3] == "single":
        profile(max_n, t)
        return
    for degree in range(max(2, 4 * ((t + 1) // 2)), max_n + 1, 2):
        profile(degree, t)


if __name__ == "__main__":
    main()
