#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Function-field probe for Erdős #385 over F_q[T], q prime.

Analogue (see DOOR-FF-ERDOS-385.md):  a monic f of degree n is GOOD if some monic g != f of
degree n with deg(f - g) < mfd(g) is reducible, where mfd(g) = least degree of an irreducible
factor of g.  Otherwise f is BAD (the analogue of F(n) <= n, OEIS A322293).

Equivalent witness form: f is good iff some monic irreducible P with deg P <= n/2 and P not
dividing f has quotient (f div P) free of irreducible factors of degree < deg P.

For each n we print: #bad f, and how many f fail the two stronger analogues:
  A(f) = largest witness degree mfd(g) over covering g  (#385(ii) analogue: A(f) -> infinity);
  top  = f has a covering g with mfd(g) = floor(n/2)        (sqrt(n) variant analogue).

Usage: erdos385-ff-probe.py q nmax [--list]
"""
import sys

import numpy as np


def digits(q, d):
    """All monic degree-d polys as coefficient arrays (N, d+1), low degree first."""
    N = q**d
    idx = np.arange(N, dtype=np.int64)
    out = np.empty((N, d + 1), dtype=np.int64)
    for i in range(d):
        out[:, i] = idx % q
        idx = idx // q
    out[:, d] = 1
    return out


def encode(q, coeffs):
    """Index of monic polys from coefficient arrays (N, d+1); leading 1 dropped."""
    d = coeffs.shape[1] - 1
    w = q ** np.arange(d, dtype=np.int64)
    return coeffs[:, :d] @ w


def mfd_table(q, nmax):
    """mfd[d][i] = least irreducible-factor degree of monic deg-d poly i, 0 if irreducible."""
    mfd = {0: np.zeros(1, dtype=np.int64)}
    irr = {}
    for d in range(1, nmax + 1):
        m = np.zeros(q**d, dtype=np.int64)
        for e in range(1, d // 2 + 1):
            H = digits(q, d - e)
            for p in irr[e]:
                prod = np.zeros((H.shape[0], d + 1), dtype=np.int64)
                for i, c in enumerate(p):
                    if c:
                        prod[:, i : i + d - e + 1] += c * H
                ix = encode(q, prod % q)
                hit = ix[m[ix] == 0]
                m[hit] = e
        mfd[d] = m
        irr[d] = [row for row in digits(q, d)[m == 0]]
    return mfd


def analyse(q, n, m, listing=False):
    N = q**n
    idx = np.arange(N, dtype=np.int64)
    good = np.zeros(N, dtype=bool)
    A = np.zeros(N, dtype=np.int64)
    for k in range(1, n // 2 + 1):
        sel = m == k
        pref = idx // q**k
        cnt = np.bincount(pref[sel], minlength=q ** (n - k))
        c = cnt[pref] - sel.astype(np.int64)
        cov = c >= 1
        good |= cov
        A[cov] = k
    top = A == n // 2
    bad = np.nonzero(~good)[0]
    if listing and len(bad):
        D = digits(q, n)
        for b in bad[:20]:
            terms = [f"{c}T^{i}" if i else str(c) for i, c in enumerate(D[b]) if c]
            print("     bad f =", " + ".join(reversed(terms)))
    return len(bad), int((good & (A < n // 2)).sum()), int(A[good].min()) if good.any() else 0


def main():
    q, nmax = int(sys.argv[1]), int(sys.argv[2])
    listing = "--list" in sys.argv
    mfd = mfd_table(q, nmax)
    print(f"q = {q}:  n | #bad f | #good f with no top-degree witness | min A(f) over good f")
    for n in range(2, nmax + 1):
        nb, nt, amin = analyse(q, n, mfd[n], listing)
        print(f"  n={n:>2} | {nb:>7} | {nt:>8} | {amin}")


if __name__ == "__main__":
    main()
