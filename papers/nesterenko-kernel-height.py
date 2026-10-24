#!/usr/bin/env -S uv run --quiet --with cypari2 python3
"""
Does clearing denominators really inflate the Siegel height in Nesterenko's
auxiliary construction for the odd-zeta extension, or do the denominators cancel
inside the solution lattice?

Functions: q, E2, E4, E6, h.  Monomials of total degree <= d: s of them.
Equations: [q^i] P = 0 for i < r = s // 2.  The integer solutions form the
saturated lattice K = ker(T) cap Z^s, and the smallest solution has
log-size ~ log H(K) / dim K (Bombieri-Vaaler), where H(K) = sqrt(det(K^T K)).

  h = g_{0,3} = sum sigma_{-3}(n) q^n      (denominators n^3; the odd-zeta case)
  h = c0      = sum sigma_0(n) q^n         (integer control, same shape)

Nesterenko's regime needs log H(K)/dim K = O(d log d).  If the g_{0,3} row is
~ (r / dim K) * 3 r while the control stays small, the loss is real.
"""

import math
import sys
from fractions import Fraction
from itertools import combinations_with_replacement

import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9, silent=True)


def sigma(k: int, n: int) -> int:
    return sum(d**k for d in range(1, n + 1) if n % d == 0)


def series(N: int, kind: str) -> list[Fraction]:
    if kind == "E2":
        return [Fraction(1)] + [Fraction(-24 * sigma(1, n)) for n in range(1, N)]
    if kind == "E4":
        return [Fraction(1)] + [Fraction(240 * sigma(3, n)) for n in range(1, N)]
    if kind == "E6":
        return [Fraction(1)] + [Fraction(-504 * sigma(5, n)) for n in range(1, N)]
    if kind == "g03":
        return [Fraction(0)] + [Fraction(sigma(3, n), n**3) for n in range(1, N)]
    if kind == "c0":
        return [Fraction(0)] + [Fraction(sigma(0, n)) for n in range(1, N)]
    raise ValueError(kind)


def mul(a, b, N):
    out = [Fraction(0)] * N
    for i, x in enumerate(a):
        if x:
            for j in range(N - i):
                if b[j]:
                    out[i + j] += x * b[j]
    return out


def kernel_height(d: int, h: str) -> tuple[int, int, float, float]:
    names = ["q", "E2", "E4", "E6", h]
    monos = [m for k in range(d + 1) for m in combinations_with_replacement(range(5), k)]
    s = len(monos)
    r = s // 2
    base = {nm: series(r, nm) for nm in names[1:]}
    cols = []
    for m in monos:
        f = [Fraction(1)] + [Fraction(0)] * (r - 1)
        shift = 0
        for v in m:
            if v == 0:
                shift += 1
            else:
                f = mul(f, base[names[v]], r)
        cols.append([Fraction(0)] * shift + f[: r - shift] if shift < r else [Fraction(0)] * r)
    rows = []
    log_clear = 0.0
    for i in range(r):
        row = [cols[j][i] for j in range(s)]
        L = 1
        for x in row:
            L = math.lcm(L, x.denominator)
        log_clear += math.log(L)
        rows.append([int(x * L) for x in row])
    A = pari.matrix(r, s, [x for row in rows for x in row])
    K = pari.matkerint(A)
    k = int(pari.matsize(K)[1])
    gram = pari.mattranspose(K) * K
    logH = float(pari.log(pari.matdet(gram))) / 2
    return s, k, logH, log_clear


def main() -> int:
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    print(f"{'d':>2} {'h':>4} {'s':>4} {'dimK':>5} {'logH/dimK':>10} {'rowclear/r':>11}")
    for d in range(2, dmax + 1):
        for h in ("c0", "g03"):
            s, k, logH, clear = kernel_height(d, h)
            print(f"{d:>2} {h:>4} {s:>4} {k:>5} {logH / k:10.3f} {clear / (s // 2):11.3f}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
