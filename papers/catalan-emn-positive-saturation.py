#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Monte Carlo intersection of EMN p-adic congruences with certified positivity.

For h with integer coefficients, F=orbit_sum(h^2) is nonnegative on the
simplex and its EMN integral is c^T(A+B*G)c.  For a chosen prime p, this
probe samples small coefficient vectors c and measures

  * the density satisfying p^k | D*c^T A*c and p^k | D*c^T B*c;
  * the best real integral before and after full p^delta saturation.

Here D is the exact common denominator of the Gram matrices and
delta=v_p(D).  This is the nonlinear positivity-intersection test missing
from catalan-emn-smith-profile.py.  It is still a local empirical probe,
not a Frobenius computation or a proof of asymptotic density.
"""

from __future__ import annotations

from fractions import Fraction
from importlib.util import module_from_spec, spec_from_file_location
from math import gcd, log, log10
from pathlib import Path
import sys

import numpy as np


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
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def gram(max_degree: int, t: int):
    """Exact Gram matrices for F=orbit_sum(h^2), matching the EMN search."""
    minimum = (t + 1) // 2
    half_degree = max_degree // 2
    basis = [
        (a, b)
        for a in range(minimum, half_degree + 1)
        for b in range(minimum, half_degree + 1)
        if a + b <= half_degree
    ]
    dimension = len(basis)
    aa = [[Fraction(0) for _ in basis] for _ in basis]
    bb = [[Fraction(0) for _ in basis] for _ in basis]
    cache = {}
    for i in range(dimension):
        for j in range(i, dimension):
            exponent = (basis[i][0] + basis[j][0], basis[i][1] + basis[j][1])
            if exponent not in cache:
                cache[exponent] = EMN.I_t(
                    EMN.orbit_sum({exponent: Fraction(1)}), t
                )
            aa[i][j] = aa[j][i] = cache[exponent][0]
            bb[i][j] = bb[j][i] = cache[exponent][1]
    denominator = 1
    for matrix in (aa, bb):
        for row in matrix:
            for entry in row:
                denominator = lcm(denominator, entry.denominator)
    ma = np.array(
        [[entry.numerator * (denominator // entry.denominator) for entry in row] for row in aa],
        dtype=np.int64,
    )
    mb = np.array(
        [[entry.numerator * (denominator // entry.denominator) for entry in row] for row in bb],
        dtype=np.int64,
    )
    catalan = 0.91596559417721901505
    real = np.array(
        [[float(aa[i][j]) + catalan * float(bb[i][j]) for j in range(dimension)]
         for i in range(dimension)],
        dtype=np.float64,
    )
    return basis, denominator, ma, mb, real


def probe(
    max_degree: int,
    t: int,
    prime: int = 2,
    trials: int = 1_000_000,
    batch_size: int = 4096,
    seed: int = 20260904,
) -> None:
    basis, denominator, ma, mb, real = gram(max_degree, t)
    delta = valuation(denominator, prime)
    if delta == 0:
        raise SystemExit(f"p={prime} does not divide D")
    modulus = prime**delta
    ma_full = ma.copy()
    mb_full = mb.copy()
    ma %= modulus
    mb %= modulus
    rng = np.random.default_rng(seed)
    counts = np.zeros(delta + 1, dtype=np.int64)
    best_all = float("inf")
    best_full = float("inf")
    best_all_vector = None
    best_full_vector = None
    full_hits = 0
    processed = 0
    while processed < trials:
        size = min(batch_size, trials - processed)
        coefficients = rng.integers(-1, 2, size=(size, len(basis)), dtype=np.int64)
        nonzero = np.any(coefficients != 0, axis=1)
        coefficients = coefficients[nonzero]
        if len(coefficients) == 0:
            continue
        qa = np.sum((coefficients @ ma) * coefficients, axis=1) % modulus
        qb = np.sum((coefficients @ mb) * coefficients, axis=1) % modulus
        values = np.einsum("bi,ij,bj->b", coefficients, real, coefficients, optimize=True)
        batch_best = int(values.argmin())
        if float(values[batch_best]) < best_all:
            best_all = float(values[batch_best])
            best_all_vector = coefficients[batch_best].copy()
        counts[0] += len(coefficients)
        local_modulus = 1
        full_mask = None
        for level in range(1, delta + 1):
            local_modulus *= prime
            mask = (qa % local_modulus == 0) & (qb % local_modulus == 0)
            counts[level] += int(mask.sum())
            if level == delta:
                full_mask = mask
        assert full_mask is not None
        if np.any(full_mask):
            full_hits += int(full_mask.sum())
            hit_indices = np.flatnonzero(full_mask)
            batch_full = int(hit_indices[np.argmin(values[full_mask])])
            if float(values[batch_full]) < best_full:
                best_full = float(values[batch_full])
                best_full_vector = coefficients[batch_full].copy()
        processed += size

    print(
        f"N={max_degree} t={t} p={prime} dim={len(basis)} trials={trials} "
        f"delta={delta} log10D={log10(denominator):.6f}"
    )
    print("k hits empirical_exponent expected_two_random_quadrics")
    for level in range(1, delta + 1):
        hits = int(counts[level])
        exponent = float("inf") if hits == 0 else -log(hits / counts[0], prime)
        print(f"{level:2d} {hits:8d} {exponent:10.4f} {2*level:10d}")
    print(f"best_all={best_all:.12g}")
    assert best_all_vector is not None
    print(f"best_all_vector={best_all_vector.tolist()}")
    if full_hits:
        assert best_full_vector is not None
        exact_a_num = int(best_full_vector @ ma_full @ best_full_vector)
        exact_b_num = int(best_full_vector @ mb_full @ best_full_vector)
        print(
            f"full_hits={full_hits} best_full={best_full:.12g} "
            f"real_penalty={best_full/best_all:.6g}"
        )
        print(f"best_full_vector={best_full_vector.tolist()}")
        print(f"a={Fraction(exact_a_num, denominator)} b={Fraction(exact_b_num, denominator)}")
        print(
            f"cleared_a_mod={exact_a_num % modulus} "
            f"cleared_b_mod={exact_b_num % modulus}"
        )
    else:
        print(f"full_hits=0 density<{1/counts[0]:.3g}")


def main() -> None:
    degree = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    t = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    prime = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    trials = int(sys.argv[4]) if len(sys.argv) > 4 else 1_000_000
    probe(degree, t, prime, trials)


if __name__ == "__main__":
    main()
