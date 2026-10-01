#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Almost-all probe for Erdős #385 (see DOOR-ALMOSTALL-ERDOS-385.md).

Per dyadic block [2^k, 2^(k+1)), prints the fraction of n with (F(n) - n)/sqrt(n) below
each threshold c.  The almost-all target "F(n) = n + (1 + o(1)) sqrt(n)" predicts these
fractions -> 0 for every fixed c < 1.  Also prints the fraction with a BALANCED SEMIPRIME
witness: m = p*q in (n - delta*sqrt(n), n), primes p <= q, p >= (1 - delta) sqrt(n).

Usage: erdos385-almostall-probe.py [N] [delta]   (defaults 10**7, 0.2)
"""
import sys

import numpy as np

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
DELTA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.2

lpf = np.zeros(N + 1, dtype=np.int64)
for p in range(2, int(N**0.5) + 1):
    if lpf[p] == 0:
        blk = lpf[p * p :: p]
        blk[blk == 0] = p
idx = np.arange(N + 1)
prime = (lpf == 0) & (idx >= 2)
lpf[prime] = idx[prime]
composite = (lpf < idx) & (idx >= 4)

val = np.where(composite, idx + lpf, 0)
F = np.zeros(N + 1, dtype=np.int64)
F[1:] = np.maximum.accumulate(val)[:-1]
ratio = (F - idx) / np.sqrt(np.maximum(idx, 1))

# balanced semiprime witness: m = p*q, q prime, lpf(m) = p >= (1 - delta) sqrt(m),
# and n - m < delta * sqrt(n).  Mark the n each such m covers.
bal = np.zeros(N + 2, dtype=np.int64)
ms = np.nonzero(composite & (lpf >= (1 - DELTA) * np.sqrt(np.maximum(idx, 1))))[0]
q = ms // lpf[ms]
ms = ms[prime[q]]
w = np.floor(DELTA * np.sqrt(ms)).astype(np.int64)
np.add.at(bal, ms + 1, 1)
np.add.at(bal, np.minimum(ms + w + 1, N + 1), -1)
covered = np.cumsum(bal)[: N + 1] > 0

cs = (0.5, 0.8, 0.9, 0.95)
print(f"N = {N:,}, delta = {DELTA}")
print("block k | " + " | ".join(f"frac (F-n)/sqrt n < {c}" for c in cs) + " | frac no balanced witness")
k = 10
while 2 ** (k + 1) <= N + 1:
    lo, hi = 2**k, 2 ** (k + 1)
    r = ratio[lo:hi]
    fr = " | ".join(f"{np.mean(r < c):.5f}" for c in cs)
    print(f"  k={k:>2} | {fr} | {1 - np.mean(covered[lo:hi]):.5f}")
    k += 1
