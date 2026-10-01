#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Erdős #385: the hyperbola criterion and the prime-pair (binary) witness count.

Hyperbola criterion (`Erdos385.Hyperbola.good_iff_exists_prime_floor`): n ≥ 5 is good
(F(n) > n) iff some prime p ≤ √n with p ∤ n has k = ⌊n/p⌋ ≥ p and minFac(k) ≥ p.  The witness is
m = p·k = n − (n mod p).

Prime-pair count W(n) = #{(p, q) primes : p < q, p·q < n < p·q + p}.  W(n) > 0 implies n good
(`Erdos385.Hyperbola.good_of_prime_pair`); `HyperbolaPrimePairs` asks for W(n) > 0 eventually.

Checks, all against numbers fixed in advance, not against this script's own output:
  1. the criterion agrees with the definition of F for 5 ≤ n ≤ 20000 (brute force);
  2. the bad n it finds include 267672 and 267680 (the two largest known, DOOR-EXCEPTIONAL A3)
     and none lies above them up to the bound;
  3. every bad n has W(n) = 0 (W > 0 forces good).
Then it reports the largest n ≤ N with W(n) = 0, and W's growth against √n / log² n.

Usage: erdos385-hyperbola-probe.py [N]   (default 10^7)
"""
import math
import sys

import numpy as np


def spf_table(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    spf[1] = 1
    for i in range(2, n + 1):
        if spf[i] == 0:
            spf[i] = i
            if i * i <= n:
                sl = spf[i * i :: i]
                sl[sl == 0] = i
                spf[i * i :: i] = sl
    return spf


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def bad_by_definition(nmax, spf):
    """Bad n per the definition: no composite m < n with m + minFac(m) > n."""
    best = 0  # running max of m + minFac(m) over composite m < n
    bad = []
    for n in range(2, nmax + 1):
        m = n - 1
        if m >= 4 and spf[m] != m:
            best = max(best, m + int(spf[m]))
        if n >= 5 and best <= n:
            bad.append(n)
    return bad


def bad_by_criterion(nmax, spf, primes):
    n = np.arange(nmax + 1, dtype=np.int64)
    good = np.zeros(nmax + 1, dtype=bool)
    for p in primes:
        if p * p > nmax:
            break
        k = n // p
        ok = (n % p != 0) & (k >= p)
        idx = np.nonzero(ok)[0]
        good[idx] |= spf[k[idx]] >= p
    return [int(x) for x in np.nonzero(~good)[0] if x >= 5]


def prime_pair_counts(nmax, primes):
    diff = np.zeros(nmax + 2, dtype=np.int32)
    is_p = np.zeros(nmax + 1, dtype=bool)
    is_p[primes[primes <= nmax]] = True
    for p in primes:
        if p * p >= nmax:
            break
        qs = primes[(primes > p) & (primes * p < nmax)]
        lo = p * qs + 1
        hi = np.minimum(p * qs + p, nmax + 1)  # n ranges over (pq, pq + p)
        np.add.at(diff, lo, 1)
        np.add.at(diff, hi, -1)
    return np.cumsum(diff[: nmax + 1])


def main():
    N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7
    spf = spf_table(N)
    primes = primes_upto(N)

    small = 20000
    d = bad_by_definition(small, spf)
    c = [x for x in bad_by_criterion(small, spf, primes) if x <= small]
    assert d == c, ("criterion disagrees with definition", d[:20], c[:20])
    print(f"check 1: criterion == definition on [5, {small}]  ({len(d)} bad n)")

    bad = bad_by_criterion(N, spf, primes)
    assert 267672 in bad and 267680 in bad, "known bad n missing"
    assert max(bad) == 267680, ("bad n beyond the known list", max(bad))
    print(f"check 2: {len(bad)} bad n ≤ {N}, largest {max(bad)}")

    W = prime_pair_counts(N, primes)
    assert all(W[b] == 0 for b in bad), "a bad n has a prime-pair witness"
    print("check 3: W(n) = 0 at every bad n")

    zeros = np.nonzero(W[5:] == 0)[0] + 5
    print(f"#{{n ≤ {N} : W(n) = 0}} = {len(zeros)}; largest = {int(zeros[-1])}")
    print("largest 12 such n:", [int(z) for z in zeros[-12:]])
    for e in range(3, int(math.log10(N)) + 1):
        lo, hi = 10 ** (e - 1), 10**e
        seg = W[lo:hi]
        mid = (lo + hi) / 2
        scale = math.sqrt(mid) / math.log(mid) ** 2
        print(f"  [{lo:>9}, {hi:>9}): min W = {int(seg.min()):>5}, mean W = {seg.mean():9.2f},"
              f" mean/(√n/log²n) = {seg.mean() / scale:5.2f}, zeros = {int((seg == 0).sum())}")


if __name__ == "__main__":
    main()
