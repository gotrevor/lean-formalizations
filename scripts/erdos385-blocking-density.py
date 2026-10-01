#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Erdős #385 exceptional-set door: the blocking statistic u_y(s).

For a residue s mod y# (y# = product of primes <= y), position a in [2, y] is BLOCKED if
s ≡ a (mod q) for some prime q <= a, and UNBLOCKED otherwise.  For n ≡ s (mod y#), a is
unblocked  <=>  n - a has no prime factor <= a, i.e. lpf(n - a) > a.  So a bad n (F(n) <= n)
needs n - a prime at every unblocked a.

    u_y(s) = #{a in [2, y] unblocked}       g(y) = P_s(u_y(s) = 0)

Since s mod y# <-> (s mod q)_{q <= y} by CRT, s uniform is the same as independent uniform
residues s_q.  So:
  * exact distribution of u_y for y <= 23 (enumerates all y# residues, chunked);
  * Monte Carlo for larger y (independent s_q), giving E u, P(u <= k) and the lower tail.

Usage: erdos385-blocking-density.py [--exact-max 23] [--mc 200000] [--mc-ys 29,47,97,199,499,997]
"""
import argparse
import math

import numpy as np


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return [int(p) for p in np.nonzero(s)[0]]


def exact(y, chunk=10_000_000):
    ps = primes_upto(y)
    M = math.prod(ps)
    counts = np.zeros(y + 1, dtype=np.int64)
    for lo in range(0, M, chunk):
        s = np.arange(lo, min(M, lo + chunk), dtype=np.int64)
        res = {q: s % q for q in ps}
        u = np.zeros(len(s), dtype=np.int64)
        for a in range(2, y + 1):
            blocked = np.zeros(len(s), dtype=bool)
            for q in ps:
                if q > a:
                    break
                blocked |= res[q] == (a % q)
            u += ~blocked
        counts += np.bincount(u, minlength=y + 1)
    return M, counts


def monte_carlo(y, trials, rng, batch=20_000):
    ps = primes_upto(y)
    us = []
    for lo in range(0, trials, batch):
        b = min(batch, trials - lo)
        res = {q: rng.integers(0, q, size=b) for q in ps}
        u = np.zeros(b, dtype=np.int64)
        for a in range(2, y + 1):
            blocked = np.zeros(b, dtype=bool)
            for q in ps:
                if q > a:
                    break
                blocked |= res[q] == (a % q)
            u += ~blocked
        us.append(u)
    return np.concatenate(us)


def mertens_mean(y):
    """E u_y = sum_{a=2}^{y} prod_{q <= a} (1 - 1/q)  (each q kills one class, independently)."""
    ps = primes_upto(y)
    tot, prod, i = 0.0, 1.0, 0
    for a in range(2, y + 1):
        while i < len(ps) and ps[i] <= a:
            prod *= 1 - 1 / ps[i]
            i += 1
        tot += prod
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--exact-max", type=int, default=23)
    ap.add_argument("--mc", type=int, default=200_000)
    ap.add_argument("--mc-ys", default="29,47,97,199,499,997")
    args = ap.parse_args()

    print("EXACT  y | y# | E u (exact) | E u (formula) | g(y)=P(u=0) | 1/y# | g*y# | P(u<=1) | P(u<=2) | P(u<=3)")
    for y in [p for p in primes_upto(args.exact_max) if p >= 5]:
        M, c = exact(y)
        P = c / M
        Eu = float((np.arange(len(c)) * c).sum() / M)
        cum = np.cumsum(P)
        print(f"  {y:>3} | {M:>11,} | {Eu:7.3f} | {mertens_mean(y):7.3f} | {P[0]:.3e} | {1/M:.3e} | "
              f"{c[0]:>6} | {cum[1]:.3e} | {cum[2]:.3e} | {cum[3]:.3e}")

    rng = np.random.default_rng(385)
    print(f"\nMONTE CARLO ({args.mc:,} samples)  y | E u (formula) | mean | sd | P(u<=E/2) | P(u<=E/4) | min u | y/log y")
    for y in [int(t) for t in args.mc_ys.split(",")]:
        u = monte_carlo(y, args.mc, rng)
        E = mertens_mean(y)
        print(f"  {y:>4} | {E:8.2f} | {u.mean():8.2f} | {u.std():6.2f} | {np.mean(u <= E/2):.2e} | "
              f"{np.mean(u <= E/4):.2e} | {u.min():>4} | {y/math.log(y):7.1f}")


if __name__ == "__main__":
    main()
