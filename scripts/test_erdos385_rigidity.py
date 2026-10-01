#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Data checks for the frozen statements of phase E1 (`NumberTheory/Erdos385/Rigidity.lean`).

Each test mirrors one Lean statement, evaluated by brute force on small n.  Expected values in
`test_hand_values` are worked out by hand (see comments), not captured from this file's code.

Run: scripts/test_erdos385_rigidity.py   (delegates to pytest)
"""
import sys


def lpf(m):
    if m % 2 == 0:
        return 2
    d = 3
    while d * d <= m:
        if m % d == 0:
            return d
        d += 2
    return m


def is_prime(m):
    return m >= 2 and lpf(m) == m


def composite(m):
    return m > 1 and not is_prime(m)


def F(n):
    """Erdos385.F: max of m + minFac m over composite m < n (0 if none, like sSup ∅ = 0)."""
    return max((m + lpf(m) for m in range(4, n) if composite(m)), default=0)


def bad(n):
    return F(n) <= n


def primorial(y):
    out = 1
    for p in range(2, y + 1):
        if is_prime(p):
            out *= p
    return out


def terms(n):
    """Erdos430.terms (FC PR #5261): 1 < m < n with every prime factor > n - m."""
    out = set()
    for m in range(2, n):
        k, ok = m, True
        while k > 1:
            p = lpf(k)
            if not n - m < p:
                ok = False
                break
            while k % p == 0:
                k //= p
        if ok:
            out.add(m)
    return out


def test_hand_values():
    # F(8): composites 4, 6 give 4+2, 6+2, so F(8) = 8 and 8 is bad.
    assert F(8) == 8 and bad(8)
    # F(6): only 4, 4 + 2 = 6.  Bad.
    assert F(6) == 6 and bad(6)
    # n = 10: 9 = 3^2 is composite, 9 + 3 = 12 > 10.  Good.
    assert F(10) == 12 and not bad(10)
    # FC PR #5261's own test: terms 8 = {5, 7}.
    assert terms(8) == {5, 7}


def test_F_ge_and_bad_iff_eq():
    for n in range(5, 3000):
        assert F(n) >= n
        assert bad(n) == (F(n) == n)


def test_sub_one_prime_of_bad():
    for n in range(5, 20000):
        if bad(n):
            assert is_prime(n - 1), n


def test_lemma_R():
    # primorial_dvd_of_minFac_le: y + 2 ≤ n, lpf(n - p) ≤ p for all primes p ≤ y ⇒ y# ∣ n.
    for n in range(4, 2500):
        for y in range(0, n - 1):
            if all(lpf(n - p) <= p for p in range(2, y + 1) if is_prime(p)):
                assert n % primorial(y) == 0, (n, y)


def test_R_prime():
    # exists_prime_pair_of_bad: bad n, n < y# ⇒ n - 1 prime ∧ ∃ prime p ∈ [3, y], n - p prime.
    for n in range(5, 20000):
        if not bad(n):
            continue
        y = 2
        while primorial(y) <= n:
            y += 1
        for yy in range(y, y + 5):
            assert is_prime(n - 1)
            assert any(is_prime(p) and p < n and is_prime(n - p) for p in range(3, yy + 1)), (n, yy)


def test_dichotomy():
    # primorial_dvd_or_exists_prime_pair_of_bad: bad n, y + 2 ≤ n ⇒ y# ∣ n ∨ ∃ prime p ∈ [3, y], n - p prime.
    for n in range(5, 20000):
        if not bad(n):
            continue
        for y in range(0, min(n - 1, 60)):
            assert n % primorial(y) == 0 or any(
                is_prime(p) and is_prime(n - p) for p in range(3, y + 1)
            ), (n, y)


def test_430_iff_not_bad():
    for n in range(5, 1500):
        has_composite_term = any(not is_prime(m) for m in terms(n))
        assert has_composite_term == (not bad(n)), n


if __name__ == "__main__":
    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
