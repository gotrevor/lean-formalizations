#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Expose the local rank-one structure in the positive EMN quadratic map.

For F = orbit_sum(h^2), clear the exact Gram denominator D and regard

    c |-> (c^T M_A c, c^T M_B c) mod p^delta,  delta = v_p(D).

The coefficients of these two quadratic forms make a 2-by-m integer map.
This script computes its Smith exponents and an explicit primitive row
relation u*M_A + v*M_B = 0 mod p^k at the largest possible depth k.
When the first Smith exponent is zero, the simultaneous congruence cost is

    p^(delta + max(0, delta-k)),

so k measures exactly how much of the second condition is redundant.
"""

from __future__ import annotations

from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from math import gcd
from pathlib import Path
import sys


PAPERS = Path(__file__).parent


def load(name: str, filename: str):
    spec = spec_from_file_location(name, PAPERS / filename)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


POS = load("catalan_emn_positive", "catalan-emn-positive-saturation.py")


def valuation(value: int, prime: int) -> int:
    if value == 0:
        return 10**9
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def prime_factors(value: int) -> list[int]:
    answer = []
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            answer.append(prime)
            while value % prime == 0:
                value //= prime
        prime += 1 if prime == 2 else 2
    if value > 1:
        answer.append(value)
    return answer


def quadratic_columns(ma, mb) -> list[tuple[int, int]]:
    """Coefficient columns for q(c), including 2*M_ij off the diagonal."""
    dimension = ma.shape[0]
    return [
        (
            int(ma[i, j]) * (1 if i == j else 2),
            int(mb[i, j]) * (1 if i == j else 2),
        )
        for i in range(dimension)
        for j in range(i, dimension)
    ]


def smith_exponents(columns: list[tuple[int, int]], prime: int) -> tuple[int, int]:
    delta1 = 0
    delta2 = 0
    for a, b in columns:
        delta1 = gcd(delta1, abs(a))
        delta1 = gcd(delta1, abs(b))
    for (a, b), (c, d) in combinations(columns, 2):
        delta2 = gcd(delta2, abs(a * d - b * c))
    return valuation(delta1, prime), valuation(delta2 // delta1, prime)


def primitive_relation(
    columns: list[tuple[int, int]], prime: int, limit: int
) -> tuple[int, int, int]:
    """Return maximal k <= limit and primitive (u,v) annihilating every column mod p^k."""
    pivot = next(((a, b) for a, b in columns if a % prime or b % prime), None)
    if pivot is None:
        raise ValueError("no primitive column")
    for k in range(limit, 0, -1):
        modulus = prime**k
        a, b = pivot
        if a % prime:
            u, v = (-b * pow(a, -1, modulus)) % modulus, 1
        else:
            u, v = 1, (-a * pow(b, -1, modulus)) % modulus
        if all((u * x + v * y) % modulus == 0 for x, y in columns):
            return k, u, v
    return 0, 0, 0


def inspect(degree: int, t: int) -> None:
    basis, denominator, ma, mb, _ = POS.gram(degree, t)
    columns = quadratic_columns(ma, mb)
    print(f"N={degree} t={t} hdim={len(basis)} qdim={len(columns)}")
    for prime in prime_factors(denominator):
        delta = valuation(denominator, prime)
        alpha1, alpha2 = smith_exponents(columns, prime)
        k, u, v = primitive_relation(columns, prime, delta)
        cost = max(0, delta - alpha1) + max(0, delta - alpha2)
        predicted = delta + max(0, delta - k)
        verified = all((u * a + v * b) % (prime**k) == 0 for a, b in columns)
        print(
            f"  p={prime:2d} delta={delta:2d} smith=({alpha1:2d},{alpha2:2d}) "
            f"relation_depth={k:2d} residual={delta-k:2d} "
            f"index_exp={cost:2d} formula={predicted:2d} verified={verified}"
        )
        print(f"     relation: ({u})*A + ({v})*B == 0 mod {prime}^{k}")


def main() -> None:
    if len(sys.argv) == 3:
        inspect(int(sys.argv[1]), int(sys.argv[2]))
        return
    for degree, t in ((16, 4), (20, 4), (24, 6), (28, 6), (32, 8)):
        inspect(degree, t)


if __name__ == "__main__":
    main()
