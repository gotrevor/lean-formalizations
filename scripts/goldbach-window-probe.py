#!/usr/bin/env -S uv run --quiet --with numpy python3
"""GoldbachWindow (`Erdos385.GoldbachWindow`): every large even N is p + q with q − p in a
prescribed window [a√N, b√N].

For the window [0, 3] and three windows of width 1 (in units of √N), report the largest even N ≤ NMAX with
no representation, and the minimum representation count over the top decade.  Controls (N ≤ 20000):
the scan restricted to p ≥ N/2 − 1.5√N finds exactly the representations with q − p ≤ 3√N that a
full scan finds, and Goldbach holds.

Usage: goldbach-window-probe.py [NMAX]   (default 2·10^5)
"""
import math
import sys

import numpy as np


def main():
    nmax = int(float(sys.argv[1])) if len(sys.argv) > 1 else 200_000
    s = np.ones(nmax + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(nmax**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    widths = [(0.0, 3.0), (0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]
    last_fail = {w: None for w in widths}
    min_top = {w: math.inf for w in widths}
    for N in range(4, nmax + 1, 2):
        lo = max(2, N // 2 - math.ceil(1.5 * math.sqrt(N)) - 1)
        p = np.arange(lo, N // 2 + 1)
        ok = s[p] & s[N - p]
        gaps = (N - 2 * p[ok]) / math.sqrt(N)
        if N <= 20000:  # control: the restricted scan sees every rep with gap ≤ 3√N
            pf = np.arange(2, N // 2 + 1)
            okf = s[pf] & s[N - pf]
            gf = (N - 2 * pf[okf]) / math.sqrt(N)
            assert int((gf <= 3).sum()) == int((gaps <= 3).sum()), ("scan window too small", N)
            assert okf.any(), ("Goldbach fails", N)
        for w in widths:
            c = int(((gaps >= w[0]) & (gaps <= w[1])).sum())
            if c == 0:
                last_fail[w] = N
            if N > nmax // 10:
                min_top[w] = min(min_top[w], c)
    print("controls: restricted scan == full scan for gaps ≤ 3√N, and Goldbach, on [4, 20000]")
    for w in widths:
        print(f"  gap window [{w[0]:.2f}, {w[1]:.2f}]·√N: last failure N = {last_fail[w]},"
              f" min count on ({nmax // 10}, {nmax}] = {min_top[w]},"
              f" heuristic count at NMAX ≈ {1.32 * (w[1] - w[0]) * math.sqrt(nmax) / (2 * math.log(nmax / 2) ** 2):.1f}")
    print("The heuristic count (b − a)√N 𝔖/(2 log²(N/2)), 𝔖 ≥ 1.32, grows like √N/log² N, so")
    print("narrow windows still fail often at this height; the conjecture is asymptotic.")


if __name__ == "__main__":
    main()
